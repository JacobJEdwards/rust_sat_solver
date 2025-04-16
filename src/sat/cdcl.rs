#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::Assignment;
use crate::sat::clause::Clause;
use crate::sat::cnf;
use crate::sat::cnf::Cnf;
use crate::sat::conflict_analysis::{Analyser, Conflict};
use crate::sat::literal::Literal;
use crate::sat::propagation::Propagator;
use crate::sat::restarter::Restarter;
use crate::sat::solver::{DefaultConfig, SolutionStats, Solutions, Solver, SolverConfig};
use crate::sat::trail::Reason;
use crate::sat::trail::Trail;
use crate::sat::variable_selection::VariableSelection;
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;

#[derive(Debug, Clone)]
pub struct Cdcl<Config: SolverConfig = DefaultConfig> {
    assignment: Config::Assignment,

    propagator: Config::Propagator,

    pub cnf: Cnf<Config::Literal, Config::LiteralStorage>,

    selector: Config::VariableSelector,

    decision_level: cnf::DecisionLevel,

    trail: Trail<Config::Literal, Config::LiteralStorage>,

    restarter: Config::Restarter,

    conflict_analysis: Analyser<Config::Literal, Config::LiteralStorage>,

    conflicts_since_last_cleanup: usize,

    cleanup_interval: usize,

    cleanup_candidates: Vec<(usize, u32, f64)>, 
    cleanup_indices_to_remove: FxHashSet<usize>,
    cleanup_new_learnt_clauses: Vec<Clause<Config::Literal, Config::LiteralStorage>>, 
    cleanup_old_to_new_idx_map: FxHashMap<usize, usize>,
}

impl<Config: SolverConfig> Cdcl<Config> {
    pub fn all_assigned(&self) -> bool {
        self.trail.len() == self.cnf.num_vars
    }

    fn should_restart(&mut self) -> bool {
        #[allow(clippy::cast_precision_loss)]
        let conflict_rate = self.restarter.num_restarts() as f64 / self.trail.len() as f64;
        self.restarter.should_restart() || conflict_rate > 0.1
    }

    fn add_propagation(&mut self, lit: Config::Literal, c_ref: usize) {
        self.trail
            .push(lit, self.decision_level, Reason::Clause(c_ref));
    }

    pub fn add_clause(&mut self, clause: Clause<Config::Literal, Config::LiteralStorage>) {
        if clause.is_empty() || clause.is_tautology() {
            return;
        }

        let c_ref = self.cnf.len();
        
        self.cnf.add_clause(clause);
        self.propagator.add_clause(&self.cnf[c_ref], c_ref);
    }

    const fn should_clean_db(&self) -> bool {
        self.conflicts_since_last_cleanup >= self.cleanup_interval
    }

    fn clean_clause_db(&mut self) {
        let learnt_start_idx = self.cnf.non_learnt_idx;
        if self.cnf.len() <= learnt_start_idx {
            return; 
        }

        let num_learnt_initial = self.cnf.len() - learnt_start_idx;

        self.cleanup_candidates.clear();

        let locked_clauses = self.trail.get_locked_clauses(); 

        for idx in learnt_start_idx..self.cnf.len() {
            if !locked_clauses.contains(&idx) {
                let clause = &self.cnf[idx];
                self.cleanup_candidates.push((idx, clause.lbd, clause.activity()));
            }
        }

        let candidates = &mut self.cleanup_candidates;

        if candidates.is_empty() {
            return; 
        }

        let num_candidates = candidates.len();
        let num_to_remove = num_candidates / 2;

        if num_to_remove == 0 {
            return;
        }

        let comparison = |a: &(usize, u32, f64), b: &(usize, u32, f64)| {
            let (_, lbd_a, act_a) = a;
            let (_, lbd_b, act_b) = b;

            let keep_a = *lbd_a <= 2;
            let keep_b = *lbd_b <= 2;

            if keep_a && !keep_b { return std::cmp::Ordering::Greater; }
            if !keep_a && keep_b { return std::cmp::Ordering::Less;    }

            match lbd_b.cmp(lbd_a) {
                std::cmp::Ordering::Equal => act_a.partial_cmp(act_b).unwrap_or(std::cmp::Ordering::Equal), // Lower activity first
                other => other,
            }
        };

        candidates.select_nth_unstable_by(num_to_remove, comparison);

        self.cleanup_indices_to_remove.clear();
        for (idx, _, _) in &candidates[..num_to_remove] {
            self.cleanup_indices_to_remove.insert(*idx);
        }
        
        let indices_to_remove = &self.cleanup_indices_to_remove;

        self.cleanup_new_learnt_clauses.clear();
        self.cleanup_old_to_new_idx_map.clear();

        let mut current_new_idx = learnt_start_idx;
        for old_idx in learnt_start_idx..self.cnf.len() {
            if !indices_to_remove.contains(&old_idx) {
                
                self.cleanup_new_learnt_clauses.push(self.cnf[old_idx].clone());
                self.cleanup_old_to_new_idx_map.insert(old_idx, current_new_idx);
                current_new_idx += 1;
            }
        }

        let new_total_len = learnt_start_idx + self.cleanup_new_learnt_clauses.len();

        self.cnf.clauses.truncate(learnt_start_idx);
        self.cnf.clauses.append(&mut self.cleanup_new_learnt_clauses);

        self.trail.remap_clause_indices(&self.cleanup_old_to_new_idx_map);

        self.propagator.cleanup_learnt(learnt_start_idx);
        for new_idx in learnt_start_idx..new_total_len {
            self.propagator.add_clause(&self.cnf[new_idx], new_idx);
        }

        self.conflicts_since_last_cleanup = 0;
    }    
    fn decay_clause_activities(&mut self) {
        for clause in &mut self.cnf.clauses[self.cnf.non_learnt_idx..] {
            clause.decay_activity(0.95);
        }
    }
    
    fn bump_involved_clause_activities(&mut self, c_ref: usize) {
        let clause = &mut self.cnf[c_ref];
        
        clause.bump_activity(1.0);
    }
}

impl<Config: SolverConfig> Solver<Config> for Cdcl<Config> {
    fn new(cnf: Cnf<Config::Literal, Config::LiteralStorage>) -> Self {
        let propagator = Propagator::new(&cnf);
        let vars = &cnf.lits;
        let selector = Config::VariableSelector::new(cnf.num_vars, vars, &cnf.clauses);
        let analysis = Analyser::new(cnf.num_vars);
        
        let mut cleanup_indices_to_remove =  FxHashSet::default();
        cleanup_indices_to_remove.reserve(64);
        
        let mut cleanup_old_to_new_idx_map = FxHashMap::default();
        cleanup_old_to_new_idx_map.reserve(64);

        Self {
            assignment: Assignment::new(cnf.num_vars),
            trail: Trail::new(&cnf),
            propagator,
            cnf,
            selector,
            restarter: Restarter::new(),
            decision_level: 0,
            conflict_analysis: analysis,
            conflicts_since_last_cleanup: 0,
            cleanup_interval: 10,
            cleanup_indices_to_remove,
            cleanup_old_to_new_idx_map,
            cleanup_candidates: Vec::with_capacity(64),
            cleanup_new_learnt_clauses: Vec::with_capacity(64),
        }
    }

    fn solve(&mut self) -> Option<Solutions> {
        if self.cnf.is_empty() {
            return Some(Solutions::default());
        }

        if self.propagator.propagate(&mut self.trail, &mut self.assignment, &mut self.cnf).is_some() {
            return None;
        }

        if self.cnf.iter().any(Clause::is_empty) {
            return None;
        }

        loop {
            if let Some(c_ref) =
                self.propagator
                    .propagate(&mut self.trail, &mut self.assignment, &mut self.cnf)
            {
                self.conflicts_since_last_cleanup += 1;
                self.decay_clause_activities();

                let (conflict, to_bump) = self.conflict_analysis.analyse_conflict(
                    &self.cnf,
                    &self.trail,
                    &self.assignment,
                    c_ref,
                );
                
                self.conflict_analysis.reset();

                match conflict {
                    Conflict::Ground => return None,
                    Conflict::Unit(clause) => {
                        self.trail.backstep_to(&mut self.assignment, 0);
                        self.decision_level = 0;
                        
                        let lit = clause[0];
                        self.add_propagation(lit, c_ref);
                    }

                    Conflict::Learned(assert_idx, mut clause) => {
                        clause.swap(0, assert_idx);
                        let asserting_lit = clause[0];

                        let bt_level = clause
                            .iter()
                            .skip(1)
                            .map(|lit| self.trail.level(lit.variable()))
                            .max()
                            .unwrap_or(0);

                        clause.calculate_lbd(&self.trail);
                        clause.is_learnt = true;
                        
                        clause.bump_activity(1.0);
                        
                        self.bump_involved_clause_activities(c_ref);

                        self.trail.backstep_to(&mut self.assignment, bt_level);
                        self.decision_level = bt_level;

                        let new_clause_idx = self.cnf.len();
                        self.add_clause(clause);
                        self.add_propagation(asserting_lit, new_clause_idx);
                        
                        if self.should_clean_db() {
                            self.clean_clause_db();
                            self.conflicts_since_last_cleanup = 0;
                        }
                    }

                    Conflict::Restart(_) => {
                        self.trail.reset();
                        self.assignment.reset();
                        self.decision_level = 0;
                    }
                }
                
                self.selector.bumps(to_bump);
                self.selector.decay(0.95);

                if self.should_restart() {
                    self.trail.reset();
                    self.assignment.reset();
                    self.decision_level = 0;
                }
            }

            self.decision_level = self.decision_level.wrapping_add(1);

            if self.all_assigned() {
                return Some(self.solutions());
            }

            let lit = self.selector.pick(&self.assignment);
            
            if let Some(lit) = lit {
                self.trail.push(lit, self.decision_level, Reason::Decision);
            } else {
                return Some(self.solutions());
            }
        }
    }

    fn solutions(&self) -> Solutions {
        self.assignment.get_solutions()
    }

    fn stats(&self) -> SolutionStats {
        SolutionStats {
            conflicts: self.conflict_analysis.count,
            decisions: self.decision_level,
            propagations: self.cnf.num_vars - self.decision_level,
            restarts: self.restarter.num_restarts(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::clause::Clause;
    use crate::sat::clause_storage::LiteralStorage;
    use crate::sat::literal::PackedLiteral;

    fn get_cnf<L: Literal, S: LiteralStorage<L>>() -> Cnf<L, S> {
        Cnf {
            clauses: vec![
                Clause::new(&[L::new(1, false)]),
                Clause::new(&[L::new(2, false)]),
                Clause::new(&[L::new(3, false)]),
            ],
            num_vars: 3,
            vars: vec![1, 2, 3],
            lits: vec![L::new(1, false), L::new(2, false), L::new(3, false)],
            non_learnt_idx: 3,
        }
    }

    fn get_unsat_cnf<L: Literal, S: LiteralStorage<L>>() -> Cnf<L, S> {
        Cnf {
            clauses: vec![
                Clause::new(&[L::new(1, false)]),
                Clause::new(&[L::new(1, true)]),
            ],
            num_vars: 1,
            vars: vec![1, 1],
            lits: vec![L::new(1, false), L::new(1, true)],
            non_learnt_idx: 2,
        }
    }

    #[test]
    fn test_new() {
        let cnf = get_cnf();

        let state: Cdcl = Cdcl::new(cnf);

        println!("{state:?}");

        assert_eq!(state.cnf.num_vars, 3);
        assert_eq!(state.cnf.len(), 3);
        assert_eq!(state.trail.len(), 3);
    }

    #[test]
    fn test_solve() {
        let cnf = get_cnf();

        let mut state: Cdcl = Cdcl::new(cnf);

        assert_eq!(state.solve(), Some(Solutions::default()));
    }

    #[test]
    fn test_solve_unsat() {
        let cnf = get_unsat_cnf();

        let mut state: Cdcl<DefaultConfig> = Cdcl::new(cnf);

        assert_eq!(state.solve(), Some(Solutions::default()));
    }

    #[test]
    fn test_solve_sat() {
        let cnf = Cnf {
            clauses: vec![
                Clause::new(&[PackedLiteral::new(1, false)]),
                Clause::new(&[PackedLiteral::new(1, true)]),
            ],
            num_vars: 1,
            vars: vec![1, 1],
            lits: vec![PackedLiteral::new(1, false), PackedLiteral::new(1, true)],
            non_learnt_idx: 2,
        };

        let mut state: Cdcl = Cdcl::new(cnf);

        assert_eq!(state.solve(), Some(Solutions::new(&[1])));
    }
}

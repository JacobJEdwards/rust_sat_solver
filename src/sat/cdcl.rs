#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use std::hash::Hash;
use crate::sat::assignment::{Assignment, Solutions, VecAssignment};
use crate::sat::clause::Clause;
use crate::sat::cnf;
use crate::sat::cnf::Cnf;
use crate::sat::conflict_analysis::{Analyser, Conflict};
use crate::sat::literal::{Literal, PackedLiteral};
use crate::sat::phase_saving::SavedPhases;
use crate::sat::preprocessing::{Preprocessor, PreprocessorChain};
use crate::sat::restarter::{Luby, Restarter};
use crate::sat::solver::Solver;
use crate::sat::trail::Reason;
use crate::sat::trail::Trail;
use crate::sat::variable_selection::{VariableSelection, Vsids};
use crate::sat::watch::WatchedLiterals;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cdcl<A: Assignment = VecAssignment, V: VariableSelection = Vsids, R: Restarter = Luby, L: Literal = PackedLiteral> {
    pub assignment: A,

    pub watched_literals: WatchedLiterals,

    pub cnf: Cnf<L>,

    pub selector: V,

    pub saved_phases: SavedPhases,

    pub decision_level: cnf::DecisionLevel,

    pub trail: Trail<L>,

    pub preprocessors: PreprocessorChain,

    pub restarter: R,

    pub non_learnt_clauses_idx: usize,

    pub restart_count: usize,
}

impl<A: Assignment, V: VariableSelection, R: Restarter, L: Literal + Eq + Hash> Cdcl<A, V, R, L> {
    fn find_new_watch(&self, clause_idx: usize) -> Option<usize> {
        let clause = &self.cnf[clause_idx];

        clause
            .iter()
            .skip(2)
            .position(|&l| self.assignment.literal_value(l) != Some(false))
            .map(|i| i + 2)
    }

    fn handle_new_watch(&mut self, clause_idx: usize, new_lit_idx: usize) {
        assert!(new_lit_idx >= 2);

        let new_lit = self.cnf[clause_idx][new_lit_idx];
        let prev_lit = self.cnf[clause_idx][1];

        self.cnf[clause_idx].swap(1, new_lit_idx);
        self.watched_literals[new_lit].push(clause_idx);
        self.watched_literals[prev_lit].retain(|&mut i| i != clause_idx);
    }

    fn add_propagation(&mut self, lit: L, clause_idx: usize) {
        self.trail
            .push(lit, self.decision_level, Reason::Clause(clause_idx));
    }

    fn process_clause(&mut self, clause_idx: usize) -> Option<usize> {
        let clause = &mut self.cnf[clause_idx];

        let first = clause[0];
        let second = clause[1];

        let first_value = self.assignment.literal_value(first);

        if first_value == Some(true) {
            return None;
        }

        let second_value = self.assignment.literal_value(second);

        if second_value == Some(true) {
            return None;
        }

        match (first_value, second_value) {
            (Some(false), Some(false)) => {
                #[cfg(debug_assertions)]
                assert!(
                    clause
                        .iter()
                        .all(|&l| self.assignment.literal_value(l) == Some(false)),
                    "Clause: {clause:?} is not false, Values: {:?}, idx: {clause_idx}, trail: \
                    {:?}",
                    clause
                        .iter()
                        .map(|&l| self.assignment.literal_value(l))
                        .collect::<Vec<_>>(),
                    self.trail,
                );

                Some(clause_idx)
            }
            (None, Some(false)) => {
                self.handle_false(first, clause_idx);
                None
            }
            (Some(false), None) => {
                clause.swap(0, 1);
                self.handle_false(second, clause_idx);
                None
            }
            (Some(true), _) | (_, Some(true)) | (None, None) => !unreachable!(),
        }
    }

    fn handle_false(&mut self, other_lit: L, clause_idx: usize) {
        match self.find_new_watch(clause_idx) {
            Some(new_lit_idx) => self.handle_new_watch(clause_idx, new_lit_idx),
            None => self.add_propagation(other_lit, clause_idx),
        };
    }

    fn propagate_watch(&mut self, indices: &[usize]) -> Option<usize> {
        indices.iter().find_map(|&idx| self.process_clause(idx))
    }

    fn propagate(&mut self) -> Option<usize> {
        while self.trail.curr_idx < self.trail.len() {
            let lit = self.trail[self.trail.curr_idx].lit;
            self.trail.curr_idx += 1;
            self.assignment.assign(lit);

            let indices = &self.watched_literals[lit].clone();

            if let Some(idx) = self.propagate_watch(indices) {
                return Some(idx);
            }
        }

        None
    }

    pub fn add_preprocessor<T: Preprocessor>(&self, preprocessor: T) -> &Self {
        self.preprocessors.add_preprocessor(preprocessor);
        self
    }

    pub fn all_assigned(&self) -> bool {
        self.assignment.all_assigned()
    }

    fn should_restart(&mut self) -> bool {
        let conflict_rate = self.restart_count as f64 / self.trail.len() as f64;
        self.restarter.should_restart() || conflict_rate > 0.1
    }

    pub fn add_clause(&mut self, clause: Clause<L>) {
        if clause.is_empty() || clause.is_tautology() {
            return;
        }

        let c_ref = self.cnf.len();
        self.cnf.add_clause(clause);
        self.watched_literals.add_clause(&self.cnf[c_ref], c_ref);

        #[cfg(debug_assertions)]
        {
            let lit_1 = self.cnf[c_ref][0];
            let lit_2 = self.cnf[c_ref][1];

            assert_ne!(self.assignment.literal_value(lit_1), Some(false));
            assert_ne!(self.assignment.literal_value(lit_2), Some(false));
        }
    }
}

impl<A: Assignment, V: VariableSelection, R: Restarter, L: Literal> Solver<L> for Cdcl<A, V, R, L> {
    fn new(cnf: Cnf<L>) -> Self {
        let non_learnt_clauses_idx = cnf.len();
        let wl = WatchedLiterals::new(&cnf);
        let vars = cnf
            .clauses
            .iter()
            .flat_map(|c| c.iter().map(|l| l.variable()))
            .collect::<Vec<_>>();

        let selector = V::new(cnf.num_vars, &vars);

        Self {
            assignment: A::new(cnf.num_vars),
            trail: Trail::new(&cnf),
            watched_literals: wl,
            saved_phases: SavedPhases::new(cnf.num_vars),
            cnf,
            selector,
            restarter: R::new(),
            decision_level: 0,
            non_learnt_clauses_idx,
            preprocessors: PreprocessorChain::new(),
            restart_count: 0,
        }
    }

    fn solve(&mut self) -> Option<Solutions> {
        if self.cnf.is_empty() {
            return Some(Solutions::default());
        }

        if self.cnf.iter().any(Clause::is_empty) {
            return None;
        }

        let cnf = self.preprocessors.preprocess(&self.cnf);
        self.cnf = cnf;

        loop {
            if let Some(c_ref) = self.propagate() {
                let (conflict, to_bump) =
                    Analyser::analyse(&self.cnf, &self.trail, &self.assignment, c_ref);

                match conflict {
                    Conflict::Ground => return None,
                    Conflict::Unit(clause) => {
                        let lit = clause[0];
                        self.add_propagation(lit, c_ref);
                    }

                    Conflict::Learned(s_idx, mut clause) => {
                        clause.swap(0, s_idx);

                        let bt_level = clause
                            .iter()
                            .skip(1)
                            .map(|lit| self.trail.lit_to_level[lit.variable() as usize])
                            .min()
                            .unwrap_or(0);

                        self.trail.backstep_to(&mut self.assignment, bt_level);
                        self.decision_level = bt_level;

                        // sometimes works ?? wat
                        clause.is_learnt = true;
                        self.add_propagation(clause[0], self.cnf.len());
                        // self.add_clause(clause);
                    }

                    Conflict::Restart(clause) => {
                        self.selector.bumps(clause.iter().map(|l| l.variable()));
                        // self.add_clause(clause);
                        self.trail.backstep_to(&mut self.assignment, 0);
                        self.decision_level = 0;
                    }
                }

                self.selector.bumps(to_bump);
                self.selector.decay(0.95);

                if self.should_restart() {
                    self.trail.backstep_to(&mut self.assignment, 0);
                    self.decision_level = 0;
                }
            }

            self.decision_level += 1;

            if self.all_assigned() {
                return Some(self.solutions());
            }

            let lit = self.selector.pick(&self.assignment);

            if lit.is_none() {
                return Some(self.solutions());
            }

            let lit = lit.unwrap();

            let next = self.saved_phases.get_next(lit);

            self.saved_phases.save(lit, next);

            self.trail.push(
                L::new(lit, !next),
                self.decision_level,
                Reason::Decision,
            );
        }
    }

    fn solutions(&self) -> Solutions {
        self.assignment.get_solutions()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::clause::Clause;

    fn get_cnf() -> Cnf<PackedLiteral> {
        Cnf {
            clauses: vec![
                Clause::new(vec![PackedLiteral::new(1, false)]),
                Clause::new(vec![PackedLiteral::new(2, false)]),
                Clause::new(vec![PackedLiteral::new(3, false)]),
            ],
            num_vars: 3,
        }
    }

    fn get_unsat_cnf() -> Cnf<PackedLiteral> {
        Cnf {
            clauses: vec![
                Clause::new(vec![PackedLiteral::new(1, false)]),
                Clause::new(vec![PackedLiteral::new(1, true)]),
            ],
            num_vars: 1,
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

        let mut state: Cdcl = Cdcl::new(cnf);

        assert_eq!(state.solve(), Some(Solutions::default()));
    }

    #[test]
    fn test_solve_sat() {
        let cnf = Cnf {
            clauses: vec![
                Clause::new(vec![PackedLiteral::new(1, false)]),
                Clause::new(vec![PackedLiteral::new(1, true)]),
            ],
            num_vars: 1,
        };

        let mut state: Cdcl = Cdcl::new(cnf);

        assert_eq!(state.solve(), Some(Solutions::new(&[1])));
    }
}

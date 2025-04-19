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
use std::fmt::Debug;
use crate::sat::clause_management::ClauseManagement;

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

    manager: Config::ClauseManager,
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
}

impl<Config: SolverConfig> Solver<Config> for Cdcl<Config> {
    fn new(cnf: Cnf<Config::Literal, Config::LiteralStorage>) -> Self {
        let propagator = Propagator::new(&cnf);
        let vars = &cnf.lits;
        let selector = Config::VariableSelector::new(cnf.num_vars, vars, &cnf.clauses);
        let restarter = Restarter::new();
        let conflict_analysis = Analyser::new(cnf.num_vars);
        let manager = Config::ClauseManager::new(&cnf.clauses);

        Self {
            assignment: Assignment::new(cnf.num_vars),
            trail: Trail::new(&cnf),
            propagator,
            cnf,
            selector,
            restarter,
            decision_level: 0,
            conflict_analysis,
            manager,
        }
    }

    fn solve(&mut self) -> Option<Solutions> {
        if self.cnf.is_empty() {
            return Some(Solutions::default());
        }

        if self
            .propagator
            .propagate(&mut self.trail, &mut self.assignment, &mut self.cnf)
            .is_some()
        {
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
                self.manager.on_conflict(&mut self.cnf);

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

                        self.manager
                            .bump_involved_clause_activities(&mut self.cnf, c_ref);

                        self.trail.backstep_to(&mut self.assignment, bt_level);
                        self.decision_level = bt_level;

                        let new_clause_idx = self.cnf.len();
                        self.add_clause(clause);
                        self.add_propagation(asserting_lit, new_clause_idx);

                        if self.manager.should_clean_db() {
                            self.manager.clean_clause_db(
                                &mut self.cnf,
                                &mut self.trail,
                                &mut self.propagator,
                                &mut self.assignment,
                            );
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
            decisions: self.selector.decisions(),
            propagations: self.propagator.num_propagations(),
            restarts: self.restarter.num_restarts(),
        }
    }

    fn debug(&mut self) {
        todo!()
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

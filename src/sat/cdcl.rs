#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::{Assignment, Solutions};
use crate::sat::clause::Clause;
use crate::sat::cnf;
use crate::sat::cnf::Cnf;
use crate::sat::conflict_analysis::{Analyser, Conflict};
use crate::sat::literal::Literal;
use crate::sat::phase_saving::PhaseSelector;
use crate::sat::preprocessing::{PreprocessorChain};
use crate::sat::propagation::Propagator;
use crate::sat::restarter::Restarter;
use crate::sat::solver::{DefaultConfig, Solver, SolverConfig};
use crate::sat::trail::Reason;
use crate::sat::trail::Trail;
use crate::sat::variable_selection::VariableSelection;

// PREPROCESSING NOT IMPLEMENTED

#[derive(Debug, Clone)]
pub struct Cdcl<Config: SolverConfig = DefaultConfig> {
    pub assignment: Config::Assignment,

    pub propagator: Config::Propagator,

    pub cnf: Cnf<Config::Literal>,

    pub selector: Config::VariableSelector,

    pub saved_phases: Config::PhaseSelector,

    pub decision_level: cnf::DecisionLevel,

    pub trail: Trail<Config::Literal>,

    pub preprocessors: PreprocessorChain<Config::Literal>,

    pub restarter: Config::Restarter,

    pub non_learnt_clauses_idx: usize,

    pub restart_count: usize,
}

impl<Config: SolverConfig> Cdcl<Config> {
    pub fn all_assigned(&self) -> bool {
        self.assignment.all_assigned()
    }

    fn should_restart(&mut self) -> bool {
        let conflict_rate = self.restart_count as f64 / self.trail.len() as f64;
        self.restarter.should_restart() || conflict_rate > 0.1
    }

    fn add_propagation(&mut self, lit: Config::Literal, c_ref: usize) {
        self.trail
            .push(lit, self.decision_level, Reason::Clause(c_ref));
    }

    pub fn add_clause(&mut self, clause: Clause<Config::Literal>) {
        if clause.is_empty() || clause.is_tautology() {
            return;
        }

        let c_ref = self.cnf.len();
        self.cnf.add_clause(clause);
        self.propagator.add_clause(&self.cnf[c_ref], c_ref);

        #[cfg(debug_assertions)]
        {
            debug_assert!(!self.cnf[c_ref]
                .iter()
                .any(|l| self.assignment.literal_value(*l) == Some(false)));
            let lit_1 = self.cnf[c_ref][0];
            let lit_2 = self.cnf[c_ref][1];

            debug_assert_ne!(self.assignment.literal_value(lit_1), Some(false));
            debug_assert_ne!(self.assignment.literal_value(lit_2), Some(false));
        }
    }
}

impl<Config: SolverConfig> Solver<Config> for Cdcl<Config> {
    fn new(cnf: Cnf<Config::Literal>) -> Self {
        let non_learnt_clauses_idx = cnf.len();
        let propagator = Propagator::new(&cnf);
        let vars = cnf.vars();
        let selector = Config::VariableSelector::new(cnf.num_vars, &vars);

        Self {
            assignment: Assignment::new(cnf.num_vars),
            trail: Trail::new(&cnf),
            propagator,
            saved_phases: PhaseSelector::new(cnf.num_vars),
            cnf,
            selector,
            restarter: Restarter::new(),
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

        loop {
            if let Some(c_ref) =
                self.propagator
                    .propagate(&mut self.trail, &mut self.assignment, &mut self.cnf)
            {
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
                        // self.add_propagation(clause[0], self.cnf.len());
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

            self.saved_phases.save(Config::Literal::new(lit, next));

            self.trail.push(
                Literal::new(lit, !next),
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
    use crate::sat::literal::PackedLiteral;

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

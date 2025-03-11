#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::solver::Solver;
use crate::sat::assignment::{Assignment, Solutions, VecAssignment};
use crate::sat::clause::Clause;
use crate::sat::cnf;
use crate::sat::cnf::Cnf;
use crate::sat::conflict_analysis::{analyse_conflict, Conflict};
use crate::sat::literal::Literal;
use crate::sat::phase_saving::SavedPhases;
use crate::sat::restarter::{Luby, Restarter};
use crate::sat::trail::Reason;
use crate::sat::trail::Trail;
use crate::sat::variable_selection::{VariableSelection, Vsids};
use crate::sat::watch::WatchedLiterals;


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State<A: Assignment = VecAssignment, V: VariableSelection = Vsids, R: Restarter = Luby> {
    pub assignment: A,

    pub watched_literals: WatchedLiterals,

    pub cnf: Cnf,

    pub learned_clauses: Vec<Clause>,

    pub selector: V,

    pub saved_phases: SavedPhases,

    pub decision_level: cnf::DecisionLevel,

    pub trail: Trail,

    pub restarter: R,

}

impl<A: Assignment, V: VariableSelection, R: Restarter> State<A, V, R> {
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

        self.cnf[clause_idx].swap(1, new_lit_idx);
        let new_lit = self.cnf[clause_idx][1];
        let prev_lit = self.cnf[clause_idx][new_lit_idx];
        self.watched_literals[new_lit].push(clause_idx);
        self.watched_literals[prev_lit].retain(|&i| i != clause_idx);
    }

    fn add_propagation(&mut self, lit: Literal, clause_idx: usize) {
        self.trail.push(lit, self.decision_level, Reason::Long(clause_idx));
    }

    fn process_clause(&mut self, clause_idx: usize) -> Option<usize> {
        let clause = &self.cnf[clause_idx];

        let first = clause[0];
        let second = clause[1];

        let first_value = self.assignment.literal_value(first);

        if first_value == Some(true) {
            return None;
        }

        let second_value = self.assignment.literal_value(second);

        match (first_value, second_value) {
            (Some(false), Some(false)) => Some(clause_idx),
            (None, Some(false)) => {
                self.handle_false(first, clause_idx);
                None
            }
            (Some(false), None) => {
                self.cnf[clause_idx].swap(0, 1);
                self.handle_false(second, clause_idx);
                None
            }
            (Some(true), _) | (_, Some(true)) | (None, None) => None,
        }
    }

    fn handle_false(&mut self, other_lit: Literal, clause_idx: usize) {
        match self.find_new_watch(clause_idx) {
            Some(new_lit_idx) => self.handle_new_watch(clause_idx, new_lit_idx),
            None => self.add_propagation(other_lit, clause_idx),
        };
    }

    fn propagate_watch(&mut self, indices: &[usize]) -> Option<usize> {
        for &i in indices {
            if let Some(c_ref) = self.process_clause(i) {
                return Some(c_ref);
            }
        }

        None
    }

    fn propagate(&mut self) -> Option<usize> {
        while self.trail.curr_idx < self.trail.len() {
            let lit = self.trail[self.trail.curr_idx].lit;
            
            if self.assignment.is_assigned(lit.variable()) {
                self.trail.curr_idx += 1;
                continue;
            }
            
            self.assignment.assign(lit);
            self.trail.curr_idx += 1;
            let indices = &self.watched_literals[!lit];
            
            if let Some(c_ref) = self.propagate_watch(&indices.clone()) {
                return Some(c_ref);
            }
        }
        
        None
    }

    pub fn all_assigned(&self) -> bool {
        self.trail.len() == self.cnf.num_vars
    }
}

impl<A: Assignment + std::fmt::Debug, V: VariableSelection, R: Restarter> Solver for State<A, V, R> {
    fn new(cnf: Cnf) -> Self {
        let wl = WatchedLiterals::new(&cnf);
        let vars = cnf
            .clauses
            .iter()
            .flat_map(|c| c.iter().map(Literal::variable))
            .collect::<Vec<_>>();
        
        let selector = V::new(cnf.num_vars, &vars);

        Self {
            assignment: A::new(cnf.num_vars),
            trail: Trail::new(&cnf),
            watched_literals: wl,
            saved_phases: SavedPhases::new(cnf.num_vars),
            cnf,
            learned_clauses: Vec::default(),
            selector,
            restarter: R::new(),
            decision_level: 0,
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
            if let Some(c_ref) = self.propagate() {
                let (conflict, to_bump) = analyse_conflict(&self.cnf, &self.trail, c_ref);

                match conflict {
                    Conflict::Ground => {
                        return None
                    }
                    Conflict::Unit(clause) => {
                        let lit = clause[0];
                        self.trail.push(lit, self.decision_level, Reason::Unit(lit.variable()));
                    }
                    Conflict::Learned(dl, clause) => {
                        self.selector.bumps(clause.iter().map(Literal::variable));
                        self.learned_clauses.push(clause);
                        self.trail.backstep_to(&mut self.assignment, dl);
                        self.decision_level = dl;
                    }
                    Conflict::Restart(clause) => {
                        self.learned_clauses.push(clause);
                        self.trail.backstep_to( &mut self.assignment, 0);
                        self.decision_level = 0;
                    }
                }

                self.selector.bumps(to_bump);
                self.selector.decay(0.95);
                if self.restarter.should_restart() {
                    self.trail.backstep_to(&mut self.assignment, 0);
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

            self.trail.push(Literal::new(lit, !next), self.decision_level, Reason::Unit(lit));
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

    #[test]
    fn test_new() {
        let cnf = Cnf {
            clauses: vec![
                Clause::new(vec![Literal::new(1, false)]),
                Clause::new(vec![Literal::new(2, false)]),
                Clause::new(vec![Literal::new(3, false)]),
            ],
            num_vars: 3,
        };

        let state: State = State::new(cnf);

        assert_eq!(state.cnf.num_vars, 3);
        assert_eq!(state.cnf.len(), 3);
        assert_eq!(state.assignment.len(), 3);
        assert_eq!(state.trail.len(), 0);
        assert_eq!(state.learned_clauses.len(), 0);
    }

    #[test]
    fn test_solve() {
        let cnf = Cnf {
            clauses: vec![
                Clause::new(vec![Literal::new(1, false)]),
                Clause::new(vec![Literal::new(2, false)]),
                Clause::new(vec![Literal::new(3, false)]),
            ],
            num_vars: 3,
        };

        let mut state: State = State::new(cnf);

        assert_eq!(state.solve(), Some(Solutions::default()));
    }

    #[test]
    fn test_solve_unsat() {
        let cnf = Cnf {
            clauses: vec![
                Clause::new(vec![Literal::new(1, false)]),
                Clause::new(vec![Literal::new(1, true)]),
            ],
            num_vars: 1,
        };

        let mut state: State = State::new(cnf);

        assert_eq!(state.solve(), None);
    }

    #[test]
    fn test_solve_sat() {
        let cnf = Cnf {
            clauses: vec![
                Clause::new(vec![Literal::new(1, false)]),
                Clause::new(vec![Literal::new(1, true)]),
            ],
            num_vars: 1,
        };

        let mut state: State = State::new(cnf);

        assert_eq!(state.solve(), Some(Solutions::new(vec![1])));
    }
}
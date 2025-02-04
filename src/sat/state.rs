use crate::sat::assignment::{Assignment, Solutions};
use crate::sat::cnf;
use crate::sat::vsids::VSIDS;
use crate::sat::clause::Clause;
use crate::sat::cnf::CNF;
use crate::sat::conflict_analysis::{analyse_conflict, Conflict};
use crate::sat::literal::Literal;
use crate::sat::watch::WatchedLiterals;
use crate::sat::propagation::PropagationQueue;
use crate::sat::trail::Trail;
use crate::sat::trail::Reason;
use crate::sat::trail::Reason::Long;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct SavedPhases(Vec<Option<bool>>);

impl SavedPhases {
    fn new(n: usize) -> Self {
        Self(vec![None; n + 1])
    }

    fn save(&mut self, i: usize, b: bool) {
        self.0[i] = Some(b);
    }

    fn get_next(&self, i: usize) -> bool {
        !self.0[i].unwrap_or(false)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct State {
    pub assignment: Assignment,

    pub watched_literals: WatchedLiterals,

    pub cnf: CNF,

    pub learned_clauses: Vec<Clause>,

    pub vsids: VSIDS,

    pub saved_phases: SavedPhases,

    pub decision_level: cnf::DecisionLevel,

    pub trail: Trail,

    pub propagation_queue: PropagationQueue,
}

impl State {
    pub fn new(cnf: CNF) -> Self {
        let wl = WatchedLiterals::new(&cnf);
        let vars = cnf
            .clauses
            .iter()
            .flat_map(|c| c.iter().map(|l| l.variable()))
            .collect::<Vec<_>>();
        let vsids = VSIDS::new(&vars);

        State {
            assignment: Assignment::new(cnf.num_vars),
            trail: Trail::new(&cnf),
            watched_literals: wl,
            propagation_queue: PropagationQueue::new(&cnf),
            saved_phases: SavedPhases::new(cnf.num_vars),
            cnf,
            learned_clauses: Vec::default(),
            vsids,
            decision_level: 0,
        }
    }

    pub fn solutions(&self) -> Solutions {
        self.assignment.get_solutions()
    }

    fn find_new_watch(&self, clause_idx: usize) -> Option<usize> {
        let clause = &self.cnf[clause_idx];

        clause.iter().skip(2).position(|&l| {
            self.assignment.literal_value(l) != Some(false)
        }).map(|i| i + 2)
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
        self.propagation_queue
            .push((lit, Option::from(Long(clause_idx))));
    }

    fn process_clause(&mut self, clause_idx: usize) -> Option<usize> {
        let clause = &self.cnf[clause_idx];

        let first = clause[0];
        let second = clause[1];

        let first_value = self.assignment.literal_value(first);
        if let Some(true) = first_value { return None }
        
        let second_value = self.assignment.literal_value(second);
        
        match (first_value, second_value) {
            (Some(false), Some(false)) => {
                Some(clause_idx)
            }
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
            None => self.add_propagation(other_lit, clause_idx)
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
        while let Some((lit, _reason)) = self.propagation_queue.pop() {
            if self.assignment.is_assigned(lit.variable()) {
                continue;
            }
            
            self.assignment.assign(lit);
            self.trail.push(lit, self.decision_level, Reason::Unit(0));
            let indices = &self.watched_literals[lit];
            
            if let Some(c_ref) = self.propagate_watch(&indices.clone()) {
                return Some(c_ref);
            }
        }

        None
    }

    pub fn all_assigned(&self) -> bool {
        self.trail.len() == self.cnf.num_vars
    }

    pub fn solve(&mut self) -> Option<Solutions> {
        if self.cnf.is_empty() {
            return Some(Solutions::default());
        }

        if self.cnf.iter().any(Clause::is_empty) {
            return None;
        }

        loop {
            if let Some(c_ref) = self.propagate() {
                match analyse_conflict(&self.cnf, &self.trail, c_ref) {
                    Conflict::Ground => return None,
                    Conflict::Unit(clause) => {
                        let lit = clause[0];
                        self.decision_level += 1;
                        self.propagation_queue.push((lit, None));
                    }
                    Conflict::Learned(dl, clause) => {
                        self.vsids.bumps(clause.literals.iter().map(|l| l.variable()));
                        self.learned_clauses.push(clause);
                        self.trail.backstep_to(&mut self.assignment, dl);
                    }
                    Conflict::Restart(_) => {
                        return None;
                    }
                }
            }

            if self.all_assigned() {
                return Some(self.solutions());
            }

            let lit = self.vsids.pick(&self.assignment)?;
            let next = self.saved_phases.get_next(lit);

            self.saved_phases.save(lit, next);

            self.decision_level += 1;
            self.propagation_queue.push((Literal::new(lit, !next), None));
        }
    }
}

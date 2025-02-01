use super::assignment::{Assignment, Solutions};
use super::cnf;
use super::vsids::VSIDS;
use crate::sat::clause::Clause;
use crate::sat::cnf::CNF;
use crate::sat::literal::Literal;
use std::collections::hash_map::HashMap;
use std::collections::hash_set::HashSet;

pub type Trail = Vec<Literal>;

pub type Reason = Clause;

#[derive(Debug, Clone, PartialEq, Eq, Default, Hash, PartialOrd, Ord)]
pub struct PropagationQueue(Vec<(usize, bool, Option<Reason>)>);

impl PropagationQueue {
    pub fn new(cnf: &CNF) -> Self {
        let q = cnf
            .iter()
            .filter(|c| c.is_unit())
            .map(|c| (c[0].var, !c[0].negated, Some(c.clone())))
            .collect();

        Self(q)
    }

    pub fn push(&mut self, p: (usize, bool, Option<Reason>)) {
        self.0.push(p);
    }

    pub fn pop(&mut self) -> Option<(usize, bool, Option<Reason>)> {
        self.0.pop()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WatchedLiterals(HashMap<usize, HashSet<usize>>);

impl WatchedLiterals {
    pub fn new(cnf: &CNF) -> Self {
        let mut watched_literals = HashMap::new();
        for (i, clause) in cnf.iter().enumerate() {
            if !clause.is_unit() {
                let a = clause.watched.0;
                let b = clause.watched.1;

                watched_literals
                    .entry(clause.literals[a].var)
                    .or_insert_with(HashSet::default)
                    .insert(i);

                watched_literals
                    .entry(clause.literals[b].var)
                    .or_insert_with(HashSet::default)
                    .insert(i);
            }
        }
        Self(watched_literals)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct SavedPhases(Vec<Option<bool>>);

impl SavedPhases {
    fn new(n: usize) -> Self {
        Self(vec![Default::default(); n + 1])
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

    pub variables: HashSet<usize>,

    pub propagation_queue: PropagationQueue,
}

impl State {
    pub fn new(cnf: CNF) -> Self {
        let wl = WatchedLiterals::new(&cnf);
        let vars = cnf
            .clauses
            .iter()
            .flat_map(|c| c.iter().map(|l| l.var))
            .collect::<Vec<_>>();
        let vsids = VSIDS::new(&vars);

        State {
            assignment: Assignment::new(cnf.num_vars),
            watched_literals: wl,
            propagation_queue: PropagationQueue::new(&cnf),
            saved_phases: SavedPhases::new(cnf.num_vars),
            cnf,
            learned_clauses: Vec::default(),
            vsids,
            decision_level: 0,
            trail: Vec::default(),
            variables: vars.into_iter().collect(),
        }
    }

    pub fn solutions(&self) -> Solutions {
        self.assignment.get_solutions()
    }

    fn find_new_watch(&self, first: Literal, second: Literal, clause_idx: usize) -> Option<usize> {
        let clause = &self.cnf[clause_idx];

        clause.iter().position(|&l| {
            l != first && l != second && self.assignment.literal_value(l) != Some(false)
        })
    }

    fn handle_new_watch(&mut self, i: usize, clause_idx: usize, old: usize, new: Literal) {
        let clause = &mut self.cnf[clause_idx];

        clause.watched = (i, old);
        let l = clause[i];

        if let Some(a_clauses) = self.watched_literals.0.get_mut(&(new.var)) {
            a_clauses.insert(clause_idx);
        }

        // dont unwrap
        if let Some(l_clauses) = self.watched_literals.0.get_mut(&(l.var)) {
            l_clauses.insert(clause_idx);
        }
    }

    fn add_propagation(&mut self, var: usize, val: bool, clause_idx: usize) {
        let clause = &self.cnf[clause_idx];
        self.propagation_queue
            .push((var, val, Some(clause.clone())));
    }

    fn process_clause(&mut self, clause_idx: usize) -> Option<Clause> {
        let clause = &self.cnf[clause_idx];

        let (a, b) = clause.watched;
        let first = clause.literals[a];
        let second = clause.literals[b];

        let first_value = self.assignment.literal_value(first);
        let second_value = self.assignment.literal_value(second);

        match (first_value, second_value) {
            (Some(true), _) | (_, Some(true)) | (None, None) => None,
            (Some(false), Some(false)) => Some(clause.clone()),
            (None, Some(false)) => {
                self.handle_false(first, second, clause_idx, a);
                None
            }
            (Some(false), None) => {
                self.handle_false(second, first, clause_idx, b);
                None
            }
        }
    }

    fn handle_false(&mut self, left: Literal, right: Literal, clause_idx: usize, idx: usize) {
        match self.find_new_watch(left, right, clause_idx) {
            Some(i) => {
                self.handle_new_watch(i, clause_idx, idx, right);
            }
            None => {
                self.add_propagation(left.var, !left.negated, clause_idx);
            }
        };
    }

    fn propagate_watch(&mut self, indices: &mut Vec<usize>) -> Option<Clause> {
        while let Some(i) = indices.pop() {
            if let Some(clause) = self.process_clause(i) {
                return Some(clause);
            }
        }
        None
    }

    fn propagate(&mut self) -> Option<Clause> {
        while let Some((i, b, reason)) = self.propagation_queue.pop() {
            self.assignment.set(i, b);
            self.trail.push(Literal::new(i, !b));
            let mut indices = self
                .watched_literals
                .0
                .get(&i)
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .collect::<Vec<_>>();
            if let Some(clause) = self.propagate_watch(&mut indices) {
                return Some(clause);
            }
        }

        None
    }

    pub fn all_assigned(&self) -> bool {
        let hash_set_assignment = self
            .assignment
            .get_all_assigned()
            .into_iter()
            .collect::<HashSet<_>>();
        self.variables
            .difference(&hash_set_assignment)
            .peekable()
            .peek()
            .is_none()
    }

    pub fn solve(&mut self) -> Option<Solutions> {
        if self.cnf.is_empty() {
            return Some(Solutions::default());
        }

        if self.cnf.iter().any(|c| c.is_empty()) {
            return None;
        }

        loop {
            if let Some(c) = self.propagate() {
                todo!("Conflict resolution");
            }

            if self.all_assigned() {
                return Some(self.solutions());
            }

            let lit = self.vsids.pick(&self.assignment)?;
            let next = self.saved_phases.get_next(lit);

            self.saved_phases.save(lit, next);

            self.decision_level += 1;
            self.propagation_queue.push((lit, next, None));
        }
    }
}

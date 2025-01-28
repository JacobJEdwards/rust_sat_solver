use super::assignment::{Assignment, Solutions};
use super::cnf;
use super::vsids::VSIDS;
use crate::sat::cnf::{var_of_lit, Clause, Literal, Variable};
use std::collections::hash_map::HashMap;
use std::collections::hash_set::HashSet;

pub type Trail = Vec<Literal>;

pub type Reason = Clause;

pub type PropagationQueue = Vec<(Variable, bool, Option<Reason>)>;

#[derive(Debug, Clone, PartialEq)]
pub struct WatchedLiterals(HashMap<Variable, HashSet<usize>>);

impl WatchedLiterals {
    pub fn new(clause_db: &ClauseDB) -> Self {
        let mut watched_literals = HashMap::new();
        for (i, clause) in clause_db.iter().enumerate() {
            let (a, b) = clause.watched;
            if a == b {
                watched_literals
                    .entry(var_of_lit(clause.literals[a]))
                    .or_insert(HashSet::new())
                    .insert(i);
            } else {
                watched_literals
                    .entry(var_of_lit(clause.literals[a]))
                    .or_insert(HashSet::new())
                    .insert(i);
                watched_literals
                    .entry(var_of_lit(clause.literals[b]))
                    .or_insert(HashSet::new())
                    .insert(i);
            }
        }
        WatchedLiterals(watched_literals)
    }
}

pub type ClauseDB = Vec<Clause>;

fn init_prop_stack(clauses: &ClauseDB) -> PropagationQueue {
    clauses
        .iter()
        .filter(|c| c.watched.0 == c.watched.1)
        .map(|c| {
            (
                var_of_lit(c.literals[0]),
                c.literals[0] > 0,
                Some(c.clone()),
            )
        })
        .collect()
}

#[derive(Debug, Clone, PartialEq)]
pub struct State {
    pub assignment: Assignment,

    pub watched_literals: WatchedLiterals,

    pub clause_db: ClauseDB,

    pub learned_clauses: Vec<Clause>,

    pub vsids: VSIDS,

    pub decision_level: cnf::DecisionLevel,

    pub trail: Trail,

    pub variables: HashSet<usize>,

    pub propagation_queue: PropagationQueue,
}

impl State {
    pub fn new(cnf: &cnf::CNF) -> Self {
        let db: ClauseDB = cnf.clauses();
        let wl = WatchedLiterals::new(&db);
        let prop_stack = init_prop_stack(&db);
        let mut vsids = VSIDS::new();
        let vars = cnf.all_variables();
        
        vsids.bumps(&vars);
        let state = State {
            assignment: Assignment::new(),
            watched_literals: wl,
            clause_db: db,
            learned_clauses: Vec::new(),
            vsids,
            decision_level: 0,
            trail: Vec::new(),
            variables: vars.into_iter().collect(),
            propagation_queue: prop_stack,
        };
        state
    }

    pub fn solutions(&self) -> Solutions {
        self.assignment.get_solutions()
    }

    fn find_new_watch(&self, first: Literal, second: Literal, clause_idx: usize) -> Option<usize> {
        let clause = &self.clause_db[clause_idx];
        let mut new_watch = None;
        for (i, &l) in clause.literals.iter().enumerate() {
            if first != l && second != l {
                if let Some(false) = self.assignment.literal_value(l) {
                    continue;
                } else {
                    new_watch = Some(i);
                }
            }
        }
        new_watch
    }

    fn handle_new_watch(&mut self, i: usize, clause_idx: usize, old: usize, new: Literal) {
        self.clause_db[clause_idx].watched = (i, old);
        let l = self.clause_db[clause_idx].literals[i];

        if let Some(a_clauses) = self.watched_literals.0.get_mut(&(var_of_lit(new))) {
            a_clauses.insert(clause_idx);
        }

        // dont unwrap
        if let Some(l_clauses) = self.watched_literals.0.get_mut(&(var_of_lit(l))) {
            l_clauses.insert(clause_idx);
        }
    }

    fn add_propagation(&mut self, i: usize, clause_idx: usize) {
        let clause = &self.clause_db[clause_idx];
        self.propagation_queue.push((
            var_of_lit(clause.literals[i]),
            clause.literals[i] > 0,
            Some(clause.clone()),
        ));
    }

    fn process_clause(&mut self, clause_idx: usize) -> Option<Clause> {
        let clause = &self.clause_db[clause_idx];

        let (a, b) = clause.watched;
        let first = clause.literals[a];
        let second = clause.literals[b];

        let first_value = self.assignment.literal_value(first);
        let second_value = self.assignment.literal_value(second);

        match (first_value, second_value) {
            (Some(true), _) => None,
            (_, Some(true)) => None,
            (Some(false), Some(false)) => Some(clause.clone()),
            (None, Some(false)) => match self.find_new_watch(first, second, clause_idx) {
                Some(i) => {
                    self.handle_new_watch(i, clause_idx, a, second);
                    None
                }
                None => {
                    self.add_propagation(a, clause_idx);
                    None
                }
            },
            (Some(false), None) => match self.find_new_watch(second, first, clause_idx) {
                Some(i) => {
                    self.handle_new_watch(i, clause_idx, b, first);
                    None
                }
                None => {
                    self.add_propagation(b, clause_idx);
                    None
                }
            },
            (None, None) => None,
        }
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
            self.assignment.set(i, b, self.decision_level, reason);
            self.trail.push(if b { i as Literal } else { -(i as Literal) });
            let mut indices = self
                .watched_literals
                .0
                .get(&i)
                .map(|x| x.clone())
                .unwrap_or(HashSet::new())
                .into_iter()
                .collect::<Vec<_>>();
            if let Some(clause) = self.propagate_watch(&mut indices) {
                return Some(clause);
            }
        }
        
        None
    }

    pub fn all_assigned(&self) -> bool {
        let hash_set_assignment = self.assignment.get_all_assigned().into_iter().collect::<HashSet<_>>();
        let missing = self.variables.difference(&hash_set_assignment).collect::<Vec<_>>();
        missing.is_empty()
    }

    pub fn solve(&mut self) -> Option<Solutions> {
        if self.clause_db.is_empty() {
            return Some(Solutions::default());
        }

        if self
            .clause_db
            .iter()
            .any(|c| c.literals.is_empty())
        {
            return None;
        }

        let mut stack = Vec::new();

        stack.push(self.clone());

        while let Some(mut current_state) = stack.pop() {
            if let Some(c) = current_state.propagate() {
                println!("Conflict, {:?}", c);
                continue;
            }

            if current_state.all_assigned() {
                return Some(current_state.solutions());
            }

            let lit = current_state.vsids.pick(&current_state.assignment)?;
            // let lit = current_state.pick_random_literal();

            let mut true_branch = current_state.clone();
            true_branch.propagation_queue.push((lit, true, None));

            let mut false_branch = current_state.clone();
            false_branch.propagation_queue.push((lit, false, None));

            stack.push(false_branch);
            stack.push(true_branch);
        }

        None // No solution found
    }
    
    fn pick_random_literal(&self) -> Variable {
        let unassigned = self.variables
            .iter()
            .filter(|i| self.assignment.var_value(**i).is_none())
            .collect::<Vec<_>>();
        *unassigned[0]
    }
}

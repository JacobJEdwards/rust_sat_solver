#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::Assignment;
use crate::sat::clause::Clause;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::literal::Variable;
use crate::sat::preprocessing::PureLiteralElimination;
use crate::sat::trail::{Reason, Trail};
use itertools::Itertools;
use smallvec::SmallVec;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

pub trait Propagator<L: Literal, S: LiteralStorage<L>, A: Assignment>: Debug + Clone {
    fn new(cnf: &Cnf<L, S>) -> Self;

    fn add_clause(&mut self, clause: &Clause<L, S>, idx: usize);

    fn propagate(
        &mut self,
        trail: &mut Trail<L, S>,
        assignment: &mut A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize>;

    fn num_propagations(&self) -> usize;

    fn add_propagation(lit: L, clause_idx: usize, trail: &mut Trail<L, S>) {
        trail.push(lit, trail.decision_level(), Reason::Clause(clause_idx));
    }

    fn cleanup_learnt(&mut self, learnt_idx: usize);
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WatchedLiterals<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize = 8> {
    watches: Vec<SmallVec<[usize; N]>>,
    num_propagations: usize,
    marker: PhantomData<*const (L, S, A)>,
}

impl<L: Literal, S: LiteralStorage<L> + Debug, A: Assignment, const N: usize> Propagator<L, S, A>
    for WatchedLiterals<L, S, A, N>
{
    fn new(cnf: &Cnf<L, S>) -> Self {
        let st = vec![SmallVec::new(); cnf.num_vars * 2];

        let mut wl = Self {
            watches: st,
            num_propagations: 0,
            marker: PhantomData,
        };

        for (i, clause) in cnf
            .iter()
            .enumerate()
            .filter(|(_, c)| !c.is_unit() && !c.is_deleted())
        {
            wl.add_clause(clause, i);
        }

        wl
    }

    fn add_clause(&mut self, clause: &Clause<L, S>, idx: usize) {
        if clause.len() < 2 || clause.is_deleted() {
            return;
        }

        let a = clause[0];
        let b = clause[1];

        debug_assert_ne!(a, b);

        self[a].push(idx);
        self[b].push(idx);
    }

    fn propagate(
        &mut self,
        trail: &mut Trail<L, S>,
        assignment: &mut A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize> {
        while trail.curr_idx < trail.len() {
            let lit = trail[trail.curr_idx].lit;
            trail.curr_idx = trail.curr_idx.wrapping_add(1);
            assignment.assign(lit);
            self.num_propagations = self.num_propagations.wrapping_add(1);

            if let Some(idx) =
                self.propagate_watch(&self[lit.negated().index()].clone(), trail, assignment, cnf)
            {
                return Some(idx);
            }
        }

        None
    }

    fn num_propagations(&self) -> usize {
        self.num_propagations
    }

    fn cleanup_learnt(&mut self, learnt_idx: usize) {
        for i in &mut self.watches {
            i.retain(|&mut j| j < learnt_idx);
        }
    }
}

impl<L: Literal, S: LiteralStorage<L> + Debug, A: Assignment, const N: usize>
    WatchedLiterals<L, S, A, N>
{
    pub fn propagate_watch(
        &mut self,
        indices: &[usize],
        trail: &mut Trail<L, S>,
        assignment: &A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize> {
        indices
            .iter()
            .find_map(|&idx| self.process_clause(idx, trail, assignment, cnf))
    }

    pub fn process_clause(
        &mut self,
        clause_idx: usize,
        trail: &mut Trail<L, S>,
        assignment: &A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize> {
        let clause = &mut cnf[clause_idx];

        let first = clause[0];
        let second = clause[1];

        let first_value = assignment.literal_value(first);

        if first_value == Some(true) {
            return None;
        }

        let second_value = assignment.literal_value(second);

        match (first_value, second_value) {
            (Some(false), Some(false)) => {
                debug_assert!(
                    clause
                        .iter()
                        .all(|&l| assignment.literal_value(l) == Some(false)),
                    "Clause: {clause:?} is not false, Values: {:?}, idx: {clause_idx}, trail: \
                    {:?}",
                    clause
                        .iter()
                        .map(|&l| assignment.literal_value(l))
                        .collect_vec(),
                    trail,
                );

                Some(clause_idx)
            }
            (None, Some(false)) => {
                self.handle_false(first, clause_idx, assignment, cnf, trail);
                None
            }
            (Some(false), None) => {
                clause.swap(0, 1);
                self.handle_false(second, clause_idx, assignment, cnf, trail);
                None
            }
            (_, Some(true)) => {
                clause.swap(0, 1);
                None
            }
            (Some(true), _) | (None, None) => None,
        }
    }

    fn handle_false(
        &mut self,
        other_lit: L,
        clause_idx: usize,
        assignment: &A,
        cnf: &mut Cnf<L, S>,
        trail: &mut Trail<L, S>,
    ) {
        match Self::find_new_watch(clause_idx, cnf, assignment) {
            Some(new_lit_idx) => self.handle_new_watch(clause_idx, new_lit_idx, cnf),
            None => Self::add_propagation(other_lit, clause_idx, trail),
        }
    }

    fn find_new_watch(clause_idx: usize, cnf: &Cnf<L, S>, assignment: &A) -> Option<usize> {
        let clause = &cnf[clause_idx];

        clause
            .iter()
            .skip(2)
            .position(|&l| assignment.literal_value(l) != Some(false))
            .map(|i| i.wrapping_add(2))
    }

    fn handle_new_watch(&mut self, clause_idx: usize, new_lit_idx: usize, cnf: &mut Cnf<L, S>) {
        debug_assert!(new_lit_idx >= 2);

        let new_lit = cnf[clause_idx][new_lit_idx];
        let prev_lit = cnf[clause_idx][1];

        cnf[clause_idx].swap(1, new_lit_idx);
        self[new_lit].push(clause_idx);
        self[prev_lit].retain(|&mut i| i != clause_idx);
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> Index<usize>
    for WatchedLiterals<L, S, A, N>
{
    type Output = SmallVec<[usize; N]>;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.watches.get_unchecked(index) }
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> IndexMut<usize>
    for WatchedLiterals<L, S, A, N>
{
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.watches.get_unchecked_mut(index) }
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> Index<Variable>
    for WatchedLiterals<L, S, A, N>
{
    type Output = SmallVec<[usize; N]>;

    fn index(&self, index: Variable) -> &Self::Output {
        &self[index as usize]
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> IndexMut<Variable>
    for WatchedLiterals<L, S, A, N>
{
    fn index_mut(&mut self, index: Variable) -> &mut Self::Output {
        &mut self[index as usize]
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> Index<L>
    for WatchedLiterals<L, S, A, N>
{
    type Output = SmallVec<[usize; N]>;

    fn index(&self, index: L) -> &Self::Output {
        &self[index.index()]
    }
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment, const N: usize> IndexMut<L>
    for WatchedLiterals<L, S, A, N>
{
    fn index_mut(&mut self, index: L) -> &mut Self::Output {
        &mut self[index.index()]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct UnitSearch<L: Literal, S: LiteralStorage<L>, A: Assignment>(
    usize,
    PhantomData<(L, S, A)>,
);

impl<L: Literal, S: LiteralStorage<L>, A: Assignment> Propagator<L, S, A> for UnitSearch<L, S, A> {
    fn new(_: &Cnf<L, S>) -> Self {
        Self(0, PhantomData)
    }

    fn add_clause(&mut self, _: &Clause<L, S>, _: usize) {}

    fn propagate(
        &mut self,
        trail: &mut Trail<L, S>,
        assignment: &mut A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize> {
        loop {
            if let Some(idx) = Self::process_cnf(trail, assignment, cnf) {
                return Some(idx);
            }

            if trail.curr_idx == trail.len() {
                return None;
            }

            while trail.curr_idx < trail.len() {
                let lit = trail[trail.curr_idx].lit;
                trail.curr_idx = trail.curr_idx.wrapping_add(1);
                assignment.assign(lit);
                self.0 = self.0.wrapping_add(1);
            }
        }
    }

    fn num_propagations(&self) -> usize {
        self.0
    }

    fn cleanup_learnt(&mut self, _: usize) {}
}

enum UnitSearchResult<L: Literal> {
    Unsat(usize),
    Unit(L),
    Continue,
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment> UnitSearch<L, S, A> {
    fn process_cnf(trail: &mut Trail<L, S>, assignment: &A, cnf: &Cnf<L, S>) -> Option<usize> {
        for (idx, clause) in cnf.iter().enumerate() {
            match Self::process_clause(clause, assignment, idx) {
                UnitSearchResult::Unsat(idx) => return Some(idx),
                UnitSearchResult::Unit(lit) => {
                    Self::add_propagation(lit, idx, trail);
                }
                UnitSearchResult::Continue => {}
            }
        }

        None
    }

    fn process_clause(clause: &Clause<L, S>, assignment: &A, idx: usize) -> UnitSearchResult<L> {
        let mut unassigned = None;

        for &lit in clause.iter() {
            match assignment.literal_value(lit) {
                Some(true) => return UnitSearchResult::Continue,
                Some(false) => {}
                None => {
                    if unassigned.is_some() {
                        return UnitSearchResult::Continue;
                    }

                    unassigned = Some(lit);
                }
            }
        }

        unassigned.map_or(UnitSearchResult::Unsat(idx), |lit| {
            UnitSearchResult::Unit(lit)
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct UnitPropagationWithPureLiterals<L: Literal, S: LiteralStorage<L>, A: Assignment>(
    UnitSearch<L, S, A>,
);

impl<L: Literal, S: LiteralStorage<L>, A: Assignment> Propagator<L, S, A>
    for UnitPropagationWithPureLiterals<L, S, A>
{
    fn new(cnf: &Cnf<L, S>) -> Self {
        Self(UnitSearch::new(cnf))
    }

    fn add_clause(&mut self, clause: &Clause<L, S>, idx: usize) {
        self.0.add_clause(clause, idx);
    }

    fn propagate(
        &mut self,
        trail: &mut Trail<L, S>,
        assignment: &mut A,
        cnf: &mut Cnf<L, S>,
    ) -> Option<usize> {
        loop {
            if let Some(idx) = self.0.propagate(trail, assignment, cnf) {
                return Some(idx);
            }

            Self::find_pure_literals(trail, cnf);

            if trail.curr_idx == trail.len() {
                return None;
            }
        }
    }

    fn num_propagations(&self) -> usize {
        self.0.num_propagations()
    }

    fn cleanup_learnt(&mut self, _: usize) {}
}

impl<L: Literal, S: LiteralStorage<L>, A: Assignment> UnitPropagationWithPureLiterals<L, S, A> {
    fn find_pure_literals(trail: &mut Trail<L, S>, cnf: &Cnf<L, S>) {
        let pures = PureLiteralElimination::find_pures(&cnf.clauses);

        for &lit in &pures {
            Self::add_propagation(lit, 0, trail);
        }
    }
}

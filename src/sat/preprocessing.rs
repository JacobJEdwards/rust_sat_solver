use crate::sat::clause::Clause;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::literal::Literal;
use itertools::Itertools;
use rustc_hash::FxHashSet;
use std::fmt::Debug;
use std::sync::Arc;

/// The shape of a preprocessor
pub trait Preprocessor<L: Literal, S: LiteralStorage<L>> {
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>>;
}

impl<L: Literal, S: LiteralStorage<L>> Debug for PreprocessorChain<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreprocessorChain").finish()
    }
}

/// Allows for chaining of preprocessors.
/// Seemingly no way to cleanly get around having to use Arc and dyn
#[derive(Clone, Default)]
pub struct PreprocessorChain<L: Literal, S: LiteralStorage<L>> {
    preprocessors: Vec<Arc<dyn Preprocessor<L, S>>>,
}

impl<L: Literal, S: LiteralStorage<L>> PreprocessorChain<L, S> {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            preprocessors: Vec::new(),
        }
    }
}

impl<L: Literal, S: LiteralStorage<L>> PreprocessorChain<L, S> {
    #[must_use]
    pub fn add_preprocessor<P: Preprocessor<L, S> + 'static>(self, preprocessor: P) -> Self {
        let mut preprocessors = self.preprocessors;
        let preprocessor = Arc::new(preprocessor);
        preprocessors.push(preprocessor);
        Self { preprocessors }
    }
}

impl<L: Literal, S: LiteralStorage<L>> Preprocessor<L, S> for PreprocessorChain<L, S> {
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        self.preprocessors
            .iter()
            .fold(Vec::from(cnf), |cnf, preprocessor| {
                preprocessor.preprocess(&cnf)
            })
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct PureLiteralElimination;

impl PureLiteralElimination {
    /// O(n)
    pub fn find_pures<L: Literal, S: LiteralStorage<L>>(cnf: &[Clause<L, S>]) -> FxHashSet<L> {
        let mut pures = FxHashSet::default();
        let mut impures = FxHashSet::default();

        for clause in cnf {
            for &lit in clause.iter() {
                if impures.contains(&lit.variable()) {
                    continue;
                }

                if pures.contains(&lit.negated()) {
                    pures.remove(&lit.negated());
                    impures.insert(lit.variable());
                    continue;
                }

                pures.insert(lit);
            }
        }

        pures
    }
}

impl<L: Literal, S: LiteralStorage<L>> Preprocessor<L, S> for PureLiteralElimination {
    /// O(n), but could be more efficient
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        let mut cnf = cnf.to_vec();

        let pures = Self::find_pures(&cnf);

        let mut to_remove = Vec::new();

        for (i, clause) in cnf.iter().enumerate() {
            if clause.iter().any(|lit| pures.contains(lit)) {
                to_remove.push(i);
            }
        }

        for &i in to_remove.iter().rev() {
            cnf.remove(i);
        }

        cnf.clone()
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct SubsumptionElimination;

impl SubsumptionElimination {
    /// uses the fact the literals are sorted to do this in O(n)
    fn is_subsumed_by<L: Literal, S: LiteralStorage<L>>(
        clause: &Clause<L, S>,
        other: &Clause<L, S>,
    ) -> bool {
        let mut c_iter = clause.iter();
        let mut o_iter = other.iter();
        
        while let Some(v1) = c_iter.next() {
            if let Some(v2) = o_iter.next() {
                if v1 != v2 {
                    return false;
                }
            } else {
                break;
            }
        }
        true
    }
}

impl<L: Literal, S: LiteralStorage<L>> Preprocessor<L, S> for SubsumptionElimination {
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        let mut result = cnf.to_vec();

        let mut sorted_indices: Vec<_> = (0..result.len()).collect();
        sorted_indices.sort_by_key(|&i| result[i].len());

        let mut to_remove = Vec::new();

        for i in 0..sorted_indices.len() {
            let idx_i = sorted_indices[i];
            if to_remove.contains(&idx_i) {
                continue;
            }

            let clause_i = &cnf[idx_i];

            for &idx_j in sorted_indices.iter().skip(i.wrapping_add(1)) {
                if to_remove.contains(&idx_j) {
                    continue;
                }

                let clause_j = &cnf[idx_j];

                if clause_i.len() <= clause_j.len() && Self::is_subsumed_by(clause_i, clause_j) {
                    to_remove.push(idx_j);
                }
            }
        }

        to_remove.sort_unstable();

        for &i in to_remove.iter().rev() {
            result.remove(i);
        }

        result
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct TautologyElimination;

impl TautologyElimination {}

impl<L: Literal, S: LiteralStorage<L>> Preprocessor<L, S> for TautologyElimination {
    /// very simple, just filter tautologies
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        cnf.iter()
            .filter(|clause| !clause.is_tautology())
            .cloned()
            .collect()
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct BoundedVariableElimination;

impl BoundedVariableElimination {
    fn eliminate_variable<L: Literal, S: LiteralStorage<L>>(
        cnf: &[Clause<L, S>],
        var: L,
    ) -> Vec<Clause<L, S>> {
        let mut new_clauses = Vec::new();
        let mut pos_clauses = Vec::new();
        let mut neg_clauses = Vec::new();

        for clause in cnf {
            if clause.iter().contains(&var) {
                pos_clauses.push(clause.clone());
            } else if clause.iter().contains(&var.negated()) {
                neg_clauses.push(clause.clone());
            } else {
                new_clauses.push(clause.clone());
            }
        }

        for pos in &pos_clauses {
            for neg in &neg_clauses {
                let resolved = pos.resolve(neg, var);
                if !resolved.is_tautology() {
                    new_clauses.push(resolved);
                }
            }
        }

        new_clauses
    }
}

impl<L: Literal, S: LiteralStorage<L>> Preprocessor<L, S> for BoundedVariableElimination {
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        let mut result = cnf.to_vec();
        let vars: FxHashSet<L> = result.iter().flat_map(Clause::iter).copied().collect();

        for var in vars {
            if result.len() > 1000 {
                break;
            }
            result = Self::eliminate_variable(&result, var);
        }

        result
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct BlockedClauseElimination;

impl BlockedClauseElimination {
    fn is_blocked_clause<L: Literal, S: LiteralStorage<L> + PartialEq>(
        cnf: &[Clause<L, S>],
        clause: &Clause<L, S>,
        blocked_literal: L,
    ) -> bool {
        for other in cnf {
            if other != clause && other.iter().contains(&blocked_literal.negated()) {
                let resolvent = clause.resolve(other, blocked_literal);
                if !resolvent.is_tautology() {
                    return false;
                }
            }
        }
        true
    }
}

impl<L: Literal, S: LiteralStorage<L> + PartialEq> Preprocessor<L, S> for BlockedClauseElimination {
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        let mut result = cnf.to_vec();
        result.retain(|clause| {
            clause
                .iter()
                .any(|&lit| Self::is_blocked_clause(cnf, clause, lit))
        });
        result
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct HyperBinaryResolution;

impl HyperBinaryResolution {
    fn apply_hbr<L: Literal, S: LiteralStorage<L>>(cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        let mut result = cnf.to_vec();
        let mut binary_clauses = Vec::new();

        for clause in cnf {
            if clause.len() == 2 {
                binary_clauses.push(clause.clone());
            }
        }

        for clause in cnf {
            if clause.len() > 2 {
                for binary in &binary_clauses {
                    if let Some(resolved) = clause.resolve_binary(binary) {
                        if !resolved.is_tautology() {
                            result.push(resolved);
                        }
                    }
                }
            }
        }

        result
    }
}

impl<L: Literal, S: LiteralStorage<L>> Preprocessor<L, S> for HyperBinaryResolution {
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        Self::apply_hbr(cnf)
    }
}

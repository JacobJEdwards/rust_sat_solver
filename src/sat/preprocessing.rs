#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
//! Defines traits and implementations for preprocessing SAT formulas.
//!
//! Preprocessing techniques aim to simplify a CNF formula before handing it
//! to the main SAT solver. This can significantly reduce the search space and
//! improve solver performance. Common techniques include:
//! - Eliminating tautological clauses (e.g., `x V !x V y`).
//! - Eliminating pure literals (literals that only appear with one polarity).
//! - Eliminating subsumed clauses (e.g., if `(x V y)` exists, `(x V y V z)` is subsumed).
//!
//! This module provides:
//! - The `Preprocessor` trait, defining a common interface for preprocessing steps.
//! - `PreprocessorChain` for applying multiple preprocessors in sequence.
//! - Implementations for several common preprocessing techniques.

use crate::sat::clause::Clause;
use crate::sat::clause_storage::LiteralStorage;
use crate::sat::literal::Literal;
use rustc_hash::FxHashSet;
use std::fmt::Debug;
use std::sync::Arc;

/// Defines the interface for a CNF formula preprocessor.
///
/// A preprocessor takes a list of clauses (representing a CNF formula)
/// and returns a new list of clauses, presumably simplified or transformed
/// in a way that preserves satisfiability.
///
/// # Type Parameters
///
/// * `L`: The `Literal` type used in clauses.
/// * `S`: The `LiteralStorage` type for clauses.
pub trait Preprocessor<L: Literal, S: LiteralStorage<L>> {
    /// Applies the preprocessing technique to the given CNF formula.
    ///
    /// # Arguments
    ///
    /// * `cnf`: A slice of `Clause<L, S>` representing the input formula.
    ///
    /// # Returns
    ///
    /// A `Vec<Clause<L, S>>` representing the preprocessed formula.
    /// This new vector might contain fewer clauses, modified clauses, or new clauses.
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>>;
}

/// A chain of preprocessors, allowing multiple preprocessing techniques
/// to be applied sequentially.
///
/// Preprocessors are stored as `Arc<dyn Preprocessor<L, S>>` to allow for
/// different concrete preprocessor types in the same chain.
///
/// # Type Parameters
///
/// * `L`: The `Literal` type.
/// * `S`: The `LiteralStorage` type.
#[derive(Clone, Default)]
pub struct PreprocessorChain<L: Literal, S: LiteralStorage<L>> {
    preprocessors: Vec<Arc<dyn Preprocessor<L, S>>>,
}

/// Custom `Debug` implementation for `PreprocessorChain`.
///
/// As `dyn Preprocessor` is not `Debug`, we provide a simple placeholder debug output.
impl<L: Literal, S: LiteralStorage<L>> Debug for PreprocessorChain<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreprocessorChain")
            .field("num_preprocessors", &self.preprocessors.len())
            .finish()
    }
}

impl<L: Literal, S: LiteralStorage<L>> PreprocessorChain<L, S> {
    /// Creates a new, empty `PreprocessorChain`.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            preprocessors: Vec::new(),
        }
    }

    /// Adds a preprocessor to the chain.
    ///
    /// The preprocessor is wrapped in an `Arc` to be stored in the chain.
    /// This method consumes `self` and returns a new chain with the added preprocessor.
    ///
    /// # Arguments
    ///
    /// * `preprocessor`: An instance of a type `P` that implements `Preprocessor<L, S>`
    ///   and is `'static` (required for `dyn Trait`).
    ///
    /// # Returns
    ///
    /// A new `PreprocessorChain` with the added preprocessor.
    #[must_use]
    pub fn add_preprocessor<P: Preprocessor<L, S> + 'static>(mut self, preprocessor: P) -> Self {
        let arc_preprocessor = Arc::new(preprocessor);
        self.preprocessors.push(arc_preprocessor);
        self
    }
}

impl<L: Literal, S: LiteralStorage<L>> Preprocessor<L, S> for PreprocessorChain<L, S> {
    /// Applies each preprocessor in the chain sequentially.
    ///
    /// The output of one preprocessor becomes the input to the next.
    /// The initial input `cnf` is cloned to start the process.
    ///
    /// # Arguments
    ///
    /// * `cnf`: A slice of `Clause<L, S>` representing the input formula.
    ///
    /// # Returns
    ///
    /// A `Vec<Clause<L, S>>` representing the formula after all preprocessors
    /// in the chain have been applied.
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        self.preprocessors
            .iter()
            .fold(Vec::from(cnf), |current_cnf, preprocessor_arc| {
                preprocessor_arc.preprocess(&current_cnf)
            })
    }
}

/// Preprocessor for Pure Literal Elimination.
///
/// A pure literal is a literal that appears in the formula with only one polarity
/// (e.g., `x` appears but `!x` does not, or vice-versa).
/// If a literal `l` is pure:
/// - All clauses containing `l` can be satisfied by setting `l` to true. These clauses can be removed.
/// - Literals that are pure do not need to be part of the simplified formula sent to the solver,
///   as their assignment is determined.
///
/// This implementation removes clauses containing any pure literal.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct PureLiteralElimination;

impl PureLiteralElimination {
    /// Finds all pure literals in the given CNF formula.
    ///
    /// A literal `l` is pure if its negation `!l` does not appear in any clause
    /// while `l` itself does appear.
    ///
    /// The complexity is roughly proportional to the total number of literals in the CNF.
    ///
    /// # Arguments
    ///
    /// * `cnf`: A slice of `Clause<L, S>`.
    ///
    /// # Returns
    ///
    /// A `FxHashSet<L>` containing all pure literals found.
    pub fn find_pures<L: Literal, S: LiteralStorage<L>>(cnf: &[Clause<L, S>]) -> FxHashSet<L> {
        let mut pures = FxHashSet::default();
        let mut impures = FxHashSet::default();

        for clause in cnf {
            for &lit in clause.iter() {
                let var = lit.variable();
                if impures.contains(&var) {
                    continue;
                }

                if pures.contains(&lit.negated()) {
                    pures.remove(&lit.negated());
                    impures.insert(var);
                    pures.remove(&lit);
                } else if !impures.contains(&var) {
                    pures.insert(lit);
                }
            }
        }

        pures
    }
}

impl<L: Literal, S: LiteralStorage<L>> Preprocessor<L, S> for PureLiteralElimination {
    /// Applies pure literal elimination.
    ///
    /// 1. Finds all pure literals in the `cnf`.
    /// 2. Removes all clauses that contain any of these pure literals.
    ///    (Assigning a pure literal `l` to true satisfies any clause containing `l`.)
    ///
    /// The complexity is dominated by `find_pures` and iterating through clauses again.
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        let mut current_cnf = cnf.to_vec();

        let pures = Self::find_pures(current_cnf.as_slice());

        if pures.is_empty() {
            return current_cnf;
        }

        current_cnf.retain(|clause| !clause.iter().any(|lit| pures.contains(lit)));

        current_cnf
    }
}

/// Preprocessor for Subsumption Elimination.
///
/// A clause C1 subsumes another clause C2 if all literals of C1 are also present in C2
/// (i.e. C1 is a sub-clause of C2). If C1 subsumes C2, C2 is redundant and can be removed.
/// For example, if `(x V y)` exists, then `(x V y V z)` is subsumed.
///
/// This implementation assumes literals within clauses are sorted for efficient checking.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct SubsumptionElimination;

impl SubsumptionElimination {
    /// Checks if `clause_potential_subsumer` subsumes `clause_potential_subsumed`.
    /// Assumes literals within each clause are sorted by some consistent criteria
    /// (e.g. by `Literal::index()` or by `Variable` then `polarity`).
    ///
    /// `clause_potential_subsumer` subsumes `clause_potential_subsumed` if
    /// `literals(clause_potential_subsumer)` is a subset of `literals(clause_potential_subsumed)`.
    ///
    fn is_subset_of<L: Literal, S: LiteralStorage<L>>(
        shorter_clause: &Clause<L, S>,
        longer_clause: &Clause<L, S>,
    ) -> bool {
        if shorter_clause.len() > longer_clause.len() {
            return false; // cannot be a subset if it's longer.
        }
        if shorter_clause.is_empty() {
            return true; // empty set is a subset of any set.
        }

        let mut shorter_iter = shorter_clause.iter();
        let mut longer_iter = longer_clause.iter();

        let mut current_shorter = shorter_iter.next();
        let mut current_longer = longer_iter.next();

        while let Some(s_lit) = current_shorter {
            while let Some(l_lit) = current_longer {
                if l_lit < s_lit {
                    current_longer = longer_iter.next();
                } else {
                    break;
                }
            }

            match current_longer {
                Some(l_lit) if l_lit == s_lit => {
                    current_shorter = shorter_iter.next();
                    current_longer = longer_iter.next();
                }
                _ => {
                    return false;
                }
            }
        }
        true
    }
}

impl<L: Literal + Ord, S: LiteralStorage<L>> Preprocessor<L, S> for SubsumptionElimination
where
    for<'a> &'a L: Ord,
{
    /// Applies subsumption elimination.
    ///
    /// Iterates through pairs of clauses. If clause `C_i` subsumes `C_j`, `C_j` is marked for removal.
    /// To optimise, clauses are typically sorted by length first: a shorter clause can subsume
    /// a longer one, but not vice versa (unless they are identical, handled by duplicate removal typically).
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        let result = cnf.to_vec();
        if result.len() < 2 {
            return result;
        }

        let mut sorted_indices: Vec<usize> = (0..result.len()).collect();
        sorted_indices.sort_by_key(|&i| result[i].len());

        let mut removed_flags = vec![false; result.len()];
        let mut num_removed = 0;

        for i in 0..sorted_indices.len() {
            let idx_i = sorted_indices[i];
            if removed_flags[idx_i] {
                continue;
            }

            for &idx_j in sorted_indices.iter().skip(i + 1) {
                if removed_flags[idx_j] {
                    continue;
                }

                if Self::is_subset_of(&result[idx_i], &result[idx_j]) {
                    removed_flags[idx_j] = true;
                    num_removed += 1;
                }
            }
        }

        if num_removed == 0 {
            return result;
        }

        let mut final_clauses = Vec::with_capacity(result.len() - num_removed);
        for i in 0..result.len() {
            if !removed_flags[i] {
                final_clauses.push(result[i].clone());
            }
        }
        final_clauses
    }
}

/// Preprocessor for Tautology Elimination.
///
/// A tautological clause is a clause that contains both a literal and its negation
/// (e.g. `x V !x V y`). Such clauses are always true and can be removed from a CNF
/// formula without changing its satisfiability.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct TautologyElimination;

impl<L: Literal, S: LiteralStorage<L>> Preprocessor<L, S> for TautologyElimination {
    /// Applies tautology elimination.
    ///
    /// Filters out any clause `c` for which `c.is_tautology()` is true.
    fn preprocess(&self, cnf: &[Clause<L, S>]) -> Vec<Clause<L, S>> {
        cnf.iter()
            .filter(|clause| !clause.is_tautology())
            .cloned()
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::literal::PackedLiteral;
    use smallvec::SmallVec;

    type TestLiteral = PackedLiteral;
    type TestClauseStorage = SmallVec<[TestLiteral; 8]>;
    type TestClause = Clause<TestLiteral, TestClauseStorage>;

    fn lit(val: i32) -> TestLiteral {
        TestLiteral::from_i32(val)
    }
    fn clause(lits_dimacs: &[i32]) -> TestClause {
        lits_dimacs.iter().map(|&x| lit(x)).collect()
    }
    fn clause_sorted(lits_dimacs: &[i32]) -> TestClause {
        let mut l: Vec<TestLiteral> = lits_dimacs.iter().map(|&x| lit(x)).collect();
        l.sort();
        Clause::new(&l)
    }

    #[test]
    fn test_tautology_elimination() {
        let preprocessor = TautologyElimination;
        let cnf = vec![clause(&[1, -1, 2]), clause(&[1, 2]), clause(&[-2, 3, 2])];
        let processed_cnf = preprocessor.preprocess(&cnf);
        assert_eq!(processed_cnf.len(), 1);
        assert_eq!(processed_cnf[0], clause(&[1, 2]));
    }

    #[test]
    fn test_pure_literal_elimination() {
        let preprocessor = PureLiteralElimination;
        let cnf = vec![clause(&[1, 2]), clause(&[-2, -3]), clause(&[2, -2])];
        let processed_cnf = preprocessor.preprocess(&cnf);
        assert_eq!(processed_cnf.len(), 1);
        assert_eq!(processed_cnf[0], clause(&[2, -2]));

        let cnf_no_pures = vec![clause(&[1, 2]), clause(&[-1, -2])];
        let processed_no_pures = preprocessor.preprocess(&cnf_no_pures);
        assert_eq!(processed_no_pures.len(), 2);

        let cnf_iterative = vec![clause(&[1]), clause(&[1, -2]), clause(&[2])];
        let processed_iterative_pass1 = preprocessor.preprocess(&cnf_iterative);
        assert_eq!(processed_iterative_pass1.len(), 1);
        assert_eq!(processed_iterative_pass1[0], clause(&[2]));

        let processed_iterative_pass2 = preprocessor.preprocess(&processed_iterative_pass1);
        assert_eq!(processed_iterative_pass2.len(), 0);
    }

    #[test]
    fn test_subsumption_elimination() {
        let preprocessor = SubsumptionElimination;
        let cnf = vec![
            clause_sorted(&[1, 2]),
            clause_sorted(&[1, 2, 3]),
            clause_sorted(&[1, 3]),
            clause_sorted(&[1]),
            clause_sorted(&[4, 5]),
        ];
        let processed_cnf = preprocessor.preprocess(&cnf);

        let expected_cnf = [clause_sorted(&[1]), clause_sorted(&[4, 5])];
        let processed_set: FxHashSet<_> = processed_cnf.iter().cloned().collect();
        let expected_set: FxHashSet<_> = expected_cnf.iter().cloned().collect();
        assert_eq!(processed_set, expected_set);
        assert_eq!(processed_cnf.len(), 2);
    }

    #[test]
    fn test_preprocessor_chain() {
        let cnf_initial = vec![clause(&[1, -1, 2]), clause(&[1, 2, 3]), clause(&[1, 2])];

        let chain = PreprocessorChain::new()
            .add_preprocessor(TautologyElimination)
            .add_preprocessor(PureLiteralElimination)
            .add_preprocessor(SubsumptionElimination);

        let processed_cnf = chain.preprocess(&cnf_initial);
        assert_eq!(processed_cnf.len(), 0);
    }
}

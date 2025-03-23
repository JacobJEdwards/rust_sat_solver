use crate::sat::clause::Clause;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use std::collections::HashSet;
use std::fmt::Debug;
use std::sync::Arc;

pub trait Preprocessor<L: Literal> {
    fn preprocess(&self, cnf: &[Clause<L>]) -> Vec<Clause<L>>;
}

impl<L: Literal> Debug for PreprocessorChain<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreprocessorChain").finish()
    }
}

#[derive(Clone, Default)]
pub struct PreprocessorChain<L: Literal> {
    preprocessors: Vec<Arc<dyn Preprocessor<L>>>,
}

impl<L: Literal> PreprocessorChain<L> {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            preprocessors: Vec::new(),
        }
    }
}

impl<L: Literal> PreprocessorChain<L> {
    #[must_use]
    pub fn add_preprocessor<P: Preprocessor<L> + 'static>(
        self,
        preprocessor: P,
    ) -> Self {
        let mut preprocessors = self.preprocessors;
        let preprocessor = Arc::new(preprocessor);
        preprocessors.push(preprocessor);
        Self { preprocessors }
    }
}

impl<L: Literal> Preprocessor<L> for PreprocessorChain<L> {
    fn preprocess(&self, cnf: &[Clause<L>]) -> Vec<Clause<L>> {
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
    fn find_pures<L: Literal>(cnf: &[Clause<L>]) -> HashSet<L> {
        let mut pures = HashSet::new();
        let mut impures = HashSet::new();

        for clause in cnf.iter() {
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

impl<L: Literal> Preprocessor<L> for PureLiteralElimination {
    fn preprocess(&self, cnf: &[Clause<L>]) -> Vec<Clause<L>> {
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

        cnf.to_vec()
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct SubsumptionElimination;

impl SubsumptionElimination {
    fn is_subsumed_by<L: Literal>(clause: &Clause<L>, other: &Clause<L>) -> bool {
        clause.iter().all(|lit| other.literals.contains(lit))
    }
}

impl<L: Literal> Preprocessor<L> for SubsumptionElimination {
    fn preprocess(&self, cnf: &[Clause<L>]) -> Vec<Clause<L>> {
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

            for &idx_j in sorted_indices.iter().skip(i + 1) {
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

impl<L: Literal> Preprocessor<L> for TautologyElimination {
    fn preprocess(&self, cnf: &[Clause<L>]) -> Vec<Clause<L>> {
        cnf.iter()
            .filter(|clause| !clause.is_tautology())
            .cloned()
            .collect()
    }
}

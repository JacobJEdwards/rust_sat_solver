use crate::sat::clause::Clause;
use crate::sat::cnf::Cnf;
use crate::sat::literal::{Literal};
use std::collections::HashSet;

pub trait Preprocessor {
    fn preprocess<L: Literal>(&self, cnf: &Cnf<L>) -> Cnf<L>;
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct NilPreprocessor;

impl Preprocessor for NilPreprocessor {
    fn preprocess<L: Literal>(&self, cnf: &Cnf<L>) -> Cnf<L> {
        cnf.clone()
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct ConsPreprocessor<H, T> {
    head: H,
    tail: T,
}

impl<H, T> Preprocessor for ConsPreprocessor<H, T>
where
    H: Preprocessor,
    T: Preprocessor,
{
    fn preprocess<L: Literal>(&self, cnf: &Cnf<L>) -> Cnf<L> {
        let intermediate = self.head.preprocess(cnf);
        self.tail.preprocess(&intermediate)
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct PreprocessorChain<T: Preprocessor = NilPreprocessor>(T);

impl PreprocessorChain {
    #[must_use]
    pub const fn new() -> Self {
        Self(NilPreprocessor)
    }
}

impl <T: Preprocessor> PreprocessorChain<T> {
    pub fn add_preprocessor<P: Preprocessor>(
        self,
        preprocessor: P,
    ) -> PreprocessorChain<ConsPreprocessor<P, T>> {
        PreprocessorChain(ConsPreprocessor {
            head: preprocessor,
            tail: self.0,
        })
    }
}

impl<T: Preprocessor> Preprocessor for PreprocessorChain<T> {
    fn preprocess<L: Literal>(&self, cnf: &Cnf<L>) -> Cnf<L> {
        self.0.preprocess(cnf)
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct PureLiteralElimination;

impl PureLiteralElimination {
    fn find_pures<L: Literal>(cnf: &Cnf<L>) -> HashSet<L> {
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

impl Preprocessor for PureLiteralElimination {
    fn preprocess<L: Literal>(&self, cnf: &Cnf<L>) -> Cnf<L> {
        let mut cnf = cnf.clone();

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

        cnf
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct SubsumptionElimination;

impl SubsumptionElimination {
    fn is_subsumed_by<L: Literal>(clause: &Clause<L>, other: &Clause<L>) -> bool {
        clause.iter().all(|lit| other.literals.contains(lit))
    }
}

impl Preprocessor for SubsumptionElimination {
    fn preprocess<L: Literal>(&self, cnf: &Cnf<L>) -> Cnf<L> {
        let mut result = cnf.clone();

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

impl Preprocessor for TautologyElimination {
    fn preprocess<L: Literal>(&self, cnf: &Cnf<L>) -> Cnf<L> {
        cnf.iter()
            .filter(|clause| !clause.is_tautology())
            .cloned()
            .collect()
    }
}

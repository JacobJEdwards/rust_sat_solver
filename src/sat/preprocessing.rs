use crate::sat::clause::Clause;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use std::collections::HashSet;

pub trait Preprocessor {
    fn preprocess(&self, cnf: &Cnf) -> Cnf;
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct NilPreprocessor;

impl Preprocessor for NilPreprocessor {
    fn preprocess(&self, cnf: &Cnf) -> Cnf {
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
    fn preprocess(&self, cnf: &Cnf) -> Cnf {
        let intermediate = self.head.preprocess(cnf);
        self.tail.preprocess(&intermediate)
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct PreprocessorChain<T: Preprocessor = NilPreprocessor>(T);

impl PreprocessorChain {
    pub const fn new() -> Self {
        Self(NilPreprocessor)
    }
}

impl<T: Preprocessor> PreprocessorChain<T> {
    pub fn add<P: Preprocessor>(
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
    fn preprocess(&self, cnf: &Cnf) -> Cnf {
        self.0.preprocess(cnf)
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct PureLiteralElimination;

impl PureLiteralElimination {
    fn find_pures(cnf: &Cnf) -> HashSet<Literal> {
        let mut pures = HashSet::new();
        let mut impures = HashSet::new();

        for clause in cnf.iter() {
            for &lit in clause.iter() {
                if impures.contains(&lit.variable()) {
                    continue;
                }

                if pures.contains(&-lit) {
                    pures.remove(&-lit);
                    impures.insert(lit.variable());
                    continue;
                }

                pures.insert(lit);
            }
        }

        pures
    }
}

// not quite right !
impl Preprocessor for PureLiteralElimination {
    fn preprocess(&self, cnf: &Cnf) -> Cnf {
        let pures = Self::find_pures(cnf);

        let mut cnf = cnf.clone();
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
    fn is_subsumed_by(clause: &Clause, other: &Clause) -> bool {
        clause.iter().all(|lit| other.literals.contains(lit))
    }
}

impl Preprocessor for SubsumptionElimination {
    fn preprocess(&self, cnf: &Cnf) -> Cnf {
        let mut cnf = cnf.clone();
        let mut i = 0;

        while i < cnf.len() {
            let clause = cnf[i].clone();
            let mut j = i + 1;

            while j < cnf.len() {
                let other = cnf[j].clone();

                if Self::is_subsumed_by(&clause, &other) {
                    cnf.remove(j);
                } else {
                    j += 1;
                }
            }

            i += 1;
        }

        cnf
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct TautologyElimination;

impl TautologyElimination {
    fn is_tautology(clause: &Clause) -> bool {
        clause.iter().any(|&lit| clause.literals.contains(&-lit))
    }
}

impl Preprocessor for TautologyElimination {
    fn preprocess(&self, cnf: &Cnf) -> Cnf {
        cnf.iter()
            .filter(|clause| !Self::is_tautology(clause))
            .cloned()
            .collect()
    }
}

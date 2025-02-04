use std::ops::{Index, IndexMut};
use crate::sat::cnf::CNF;
use crate::sat::literal::Literal;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WatchedLiterals(Vec<Vec<usize>>);

impl WatchedLiterals {
    pub fn new(cnf: &CNF) -> Self {
        // let watched_literals = 
        //     cnf.iter()
        //         .enumerate()
        //         .filter(|(_, c)| !c.is_unit())
        //         .fold(vec![Vec::default(); cnf.num_vars + 1], |mut acc, (i, clause)| {
        //             let a = clause[0];
        //             let b = clause[1];
        // 
        //             acc[a.var].push(i);
        //             acc[b.var].push(i);
        // 
        //             acc
        //         });
        
        let mut watched_literals = vec![Vec::default(); cnf.num_vars + 1];
        
        for (i, clause) in cnf.iter().enumerate().filter(|(_, c)| !c.is_unit()) {
            let a = clause[0];
            let b = clause[1];
        
            watched_literals[a.variable()].push(i);
            watched_literals[b.variable()].push(i);
        }

        Self(watched_literals)
    }
}

impl Index<usize> for WatchedLiterals {
    type Output = Vec<usize>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl IndexMut<usize> for WatchedLiterals {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl Index<Literal> for WatchedLiterals {
    type Output = Vec<usize>;

    fn index(&self, index: Literal) -> &Self::Output {
        &self.0[index.variable()]
    }
}

impl IndexMut<Literal> for WatchedLiterals {
    fn index_mut(&mut self, index: Literal) -> &mut Self::Output {
        &mut self.0[index.variable()]
    }
}
use crate::sat::literal::Variable;
use rand::random;
use std::ops::{Index, IndexMut};

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct SavedPhases(Vec<Option<bool>>);

impl SavedPhases {
    pub(crate) fn new(n: usize) -> Self {
        Self(vec![None; n])
    }

    pub(crate) fn save(&mut self, i: Variable, b: bool) {
        self[i as usize] = Some(b);
    }

    pub(crate) fn reset(&mut self) {
        for i in 1..self.0.len() {
            self[i] = None;
        }
    }

    pub(crate) fn get_next(&self, i: Variable) -> bool {
        if random::<f64>() < 0.1 {
            !self.0[i as usize].unwrap_or(true)
        } else {
            self.0[i as usize].unwrap_or(true)
        }
    }
}

impl Index<usize> for SavedPhases {
    type Output = Option<bool>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl IndexMut<usize> for SavedPhases {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

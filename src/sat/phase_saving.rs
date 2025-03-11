use std::ops::{Index, IndexMut};
use rand::random;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct SavedPhases(Vec<Option<bool>>);

impl SavedPhases {
    pub(crate) fn new(n: usize) -> Self {
        Self(vec![None; n + 1])
    }

    pub(crate) fn save(&mut self, i: usize, b: bool) {
        self[i] = Some(b);

    }

    pub(crate) fn get_next(&self, i: usize) -> bool {
        if random::<f64>() < 0.1 { // 10% chance to flip polarity
            !self.0[i].unwrap_or(true)
        } else {
            self.0[i].unwrap_or(true)
        }    }
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

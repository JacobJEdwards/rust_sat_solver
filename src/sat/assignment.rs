use crate::sat::literal::Literal;
use core::ops::{Index, IndexMut};

#[derive(Debug, Clone, PartialEq, Eq, Copy, Default, Hash, PartialOrd, Ord)]
pub enum VarState {
    #[default]
    Unassigned,
    Assigned(bool),
}

impl VarState {
    pub const fn is_assigned(&self) -> bool {
        matches!(self, VarState::Assigned(_))
    }

    pub const fn is_unassigned(&self) -> bool {
        !self.is_assigned()
    }

    pub const fn is_true(&self) -> bool {
        match self {
            VarState::Assigned(b) => *b,
            _ => false,
        }
    }

    pub fn is_false(&self) -> bool {
        match self {
            VarState::Assigned(b) => !b,
            _ => false,
        }
    }
}

impl From<VarState> for Option<bool> {
    fn from(s: VarState) -> Self {
        match s {
            VarState::Assigned(b) => Some(b),
            _ => None,
        }
    }
}

impl From<Option<bool>> for VarState {
    fn from(b: Option<bool>) -> Self {
        match b {
            Some(b) => VarState::Assigned(b),
            None => VarState::Unassigned,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Assignment(Vec<VarState>);

impl Index<usize> for Assignment {
    type Output = VarState;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl IndexMut<usize> for Assignment {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

pub type Solutions = Vec<usize>;

// impl Solutions {
//     pub fn iter(&self) -> impl Iterator<Item = &usize> {
//         self.0.iter()
//     }
// }
//
// impl Solutions {
//     pub fn check(&self, i: usize) -> bool {
//         self.0.contains(&i)
//     }
//
//     pub fn empty() -> Self {
//         Solutions(HashSet::new())
//     }
// }

impl Assignment {
    pub fn new(n: usize) -> Self {
        Assignment(vec![VarState::Unassigned; n + 1])
    }

    pub fn set(&mut self, lit: usize, b: bool) {
        self[lit] = VarState::Assigned(b);
    }
    
    pub fn assign(&mut self, l: Literal) {
        self.set(l.variable(), l.polarity());
    }
    
    pub fn unassign(&mut self, i: usize) {
        self[i] = VarState::Unassigned;
    }
    
    pub fn is_assigned(&self, i: usize) -> bool {
        self.0[i].is_assigned()
    }

    pub fn get_solutions(&self) -> Solutions {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, s)| match s {
                VarState::Assigned(true) => Some(i),
                _ => None,
            })
            .collect()
    }

    pub fn get_all_assigned(&self) -> Vec<usize> {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, s)| match s {
                VarState::Assigned(_) => Some(i),
                _ => None,
            })
            .collect()
    }

    pub fn var_value(&self, i: usize) -> Option<bool> {
        self[i].into()
    }

    pub fn literal_value(&self, l: Literal) -> Option<bool> {
        self.var_value(l.variable()).map(|b| b ^ l.is_negated())
    }
}

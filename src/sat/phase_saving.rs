use crate::sat::literal::Literal;
use crate::sat::literal::Variable;
use rand::random;

pub trait PhaseSelector {
    fn new(n: usize) -> Self;
    fn save(&mut self, lit: impl Literal);
    fn reset(&mut self);
    fn get_next(&self, var: Variable) -> bool;
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct SavedPhases(Vec<Option<bool>>);

impl PhaseSelector for SavedPhases {
    fn new(n: usize) -> Self {
        Self(vec![None; n])
    }

    fn save(&mut self, lit: impl Literal) {
        self.0[lit.variable() as usize] = Some(lit.polarity());
    }

    fn reset(&mut self) {
        for i in 1..self.0.len() {
            self.0[i] = None;
        }
    }

    fn get_next(&self, i: Variable) -> bool {
        if random::<f64>() < 0.1 {
            !self.0[i as usize].unwrap_or(true)
        } else {
            self.0[i as usize].unwrap_or(true)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct RandomPhases;

impl PhaseSelector for RandomPhases {
    fn new(_: usize) -> Self {
        Self
    }
    fn save(&mut self, _: impl Literal) {}

    fn reset(&mut self) {}
    fn get_next(&self, _: Variable) -> bool {
        random::<bool>()
    }
}

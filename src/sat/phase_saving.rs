use crate::sat::literal::Literal;
use bit_vec::BitVec;
use rand::{rng, Rng};

pub trait PhaseSelector {
    fn new(n: usize) -> Self;
    fn save(&mut self, lit: impl Literal);
    fn reset(&mut self);
    fn get_next(&self, var: impl Literal) -> bool;
    fn on_conflict(&mut self);
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct SavedPhases(BitVec);

impl PhaseSelector for SavedPhases {
    fn new(n: usize) -> Self {
        Self(BitVec::from_elem(n, true))
    }

    fn save(&mut self, lit: impl Literal) {
        unsafe {
            *self.0.get_unchecked_mut(lit.variable() as usize) = lit.polarity();
        }
    }

    fn reset(&mut self) {
        self.0.set_all();
    }

    fn get_next(&self, i: impl Literal) -> bool {
        unsafe {
            let mut rng = rng();
            let phase = self.0.get_unchecked(i.variable() as usize);
            phase ^ (rng.random::<f64>() < 0.1)
        }
    }

    fn on_conflict(&mut self) {}
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct RandomPhases;

impl PhaseSelector for RandomPhases {
    fn new(_: usize) -> Self {
        Self
    }
    fn save(&mut self, _: impl Literal) {}

    fn reset(&mut self) {}
    fn get_next(&self, _: impl Literal) -> bool {
        let mut rng = rng();
        rng.random::<bool>()
    }
    fn on_conflict(&mut self) {}
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct AdaptiveSavedPhases {
    phases: BitVec,
    noise_probability: f64,
    conflict_counter: usize,
}

impl PhaseSelector for AdaptiveSavedPhases {
    fn new(n: usize) -> Self {
        Self {
            phases: BitVec::from_elem(n, true),
            noise_probability: 0.1,
            conflict_counter: 0,
        }
    }

    fn save(&mut self, lit: impl Literal) {
        unsafe {
            *self.phases.get_unchecked_mut(lit.variable() as usize) = lit.polarity();
        }
    }

    fn reset(&mut self) {
        self.phases.set_all();
    }

    fn get_next(&self, var: impl Literal) -> bool {
        unsafe {
            let phase = self.phases.get_unchecked(var.variable() as usize);
            let mut rng = rng();
            phase ^ (rng.random::<f64>() < self.noise_probability)
        }
    }

    fn on_conflict(&mut self) {
        self.conflict_counter = self.conflict_counter.wrapping_add(1);

        if self.conflict_counter % 100 == 0 {
            self.noise_probability *= 0.95;
        }
    }
}

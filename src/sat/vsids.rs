use crate::sat::assignment::Assignment;
use std::collections::hash_map::HashMap;
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct VSIDS(HashMap<usize, f64>);

const DEFAULT_DECAY: f64 = 0.95;

impl VSIDS {
    pub fn new(vars: &[usize]) -> Self {
        let mut vsids = VSIDS(HashMap::new());
        vsids.bumps(vars);
        vsids
    }

    pub fn decay(&mut self, decay: f64) {
        for (_, v) in self.0.iter_mut() {
            *v *= decay;
        }
    }

    pub fn bump(&mut self, i: usize) {
        let v = self.0.entry(i).or_insert(0.0);
        *v += 1.0;
    }

    pub fn bumps(&mut self, vars: &[usize]) {
        for &i in vars {
            self.bump(i);
        }
    }

    pub fn bumps_set(&mut self, vars: &HashSet<usize>) {
        for i in vars {
            self.bump(*i);
        }
    }

    pub fn get(&self, i: usize) -> f64 {
        *self.0.get(&i).unwrap_or(&0.0)
    }

    pub fn set(&mut self, i: usize, v: f64) {
        self.0.insert(i, v);
    }

    pub fn reset(&mut self) {
        self.0.clear();
    }

    pub fn decay_default(&mut self) {
        self.decay(DEFAULT_DECAY);
    }

    pub fn pick(&mut self, assignment: &Assignment) -> Option<usize> {
        let mut max = 0.0;
        let mut max_i = None;

        for (i, v) in self.0.iter() {
            if *v > max && assignment[*i].is_unassigned() {
                max = *v;
                max_i = Some(*i);
            }
        }
        max_i
    }
}

#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]

use crate::sat::assignment::Assignment;
use crate::sat::literal::Literal;
use fastrand::Rng;
use ordered_float::OrderedFloat;
use std::cell::RefCell;
use std::collections::BinaryHeap;
use std::fmt::Debug;
use std::ops::{Index, IndexMut};

/// A trait for variable selection strategies in SAT solvers.
pub trait VariableSelection<L: Literal>: Debug + Clone {
    /// Creates a new instance of the variable selection strategy.
    fn new<C: AsRef<[L]>>(num_vars: usize, vars: &[L], clauses: &[C]) -> Self;
    /// Picks a variable based on the current assignment.
    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L>;

    /// Bumps the activity of the given variables.
    fn bumps<T: IntoIterator<Item = L>>(&mut self, vars: T);
    /// Decays the activity of the variables.
    fn decay(&mut self, decay: f64);

    /// Returns the number of decisions made.
    fn decisions(&self) -> usize;
}

/// A structure representing a score entry in the VSIDS heap.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ScoreEntry {
    /// Ordered float must be used to ensure the ordering of the heap.
    score: OrderedFloat<f64>,
    lit_idx: usize,
}

/// A constant for the VSIDS rescale threshold.
const VSIDS_RESCALE_THRESHOLD: f64 = 1e100;
/// A constant for the VSIDS rescale factor.
const VSIDS_RESCALE_FACTOR: f64 = 1e-100;

/// A structure representing the VSIDS heap for variable selection.
#[derive(Debug, Clone)]
pub struct VsidsHeap {
    /// The current activity scores of the variables.
    scores: Vec<f64>,
    activity_inc: f64,
    /// Heap of score entries, allowing for efficient retrieval of the highest score.
    heap: BinaryHeap<ScoreEntry>,
    num_decisions: usize,
}

/// `Index` trait implementation for the VSIDS heap.
/// Allows for indexing into the scores vector.
///
/// # Safety
/// Should only be used internally and with care due to the unchecked indexing.
/// If indexed with non-arbitrary values, there is no risk of out-of-bounds access.
impl Index<usize> for VsidsHeap {
    type Output = f64;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.scores.get_unchecked(index) }
    }
}

/// `IndexMut` trait implementation for the VSIDS heap.
/// Allows for mutable indexing into the scores vector.
///
/// # Safety
/// Again, should only be used internally and with care due to the unchecked indexing.
impl IndexMut<usize> for VsidsHeap {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.scores.get_unchecked_mut(index) }
    }
}

/// `VsidsHeap` implementation.
impl VsidsHeap {
    /// Bumps the activity of a variable at the given index.
    fn bump_internal(&mut self, lit_idx: usize) {
        let score_ref = unsafe { self.scores.get_unchecked_mut(lit_idx) };
        *score_ref += self.activity_inc;
        let new_score = *score_ref;

        // Push the new score entry into the heap.
        // At this point we don't need to remove the old entry, that is handled when rescaling.
        self.heap.push(ScoreEntry {
            score: OrderedFloat(new_score),
            lit_idx,
        });
    }

    /// Rescales the scores in the heap to prevent overflow and deduplicate the scores stored in
    /// the heap.
    fn rescale_scores(&mut self) {
        // Rescale the scores to prevent overflow.
        self.scores
            .iter_mut()
            .for_each(|s| *s *= VSIDS_RESCALE_FACTOR);
        // Rescale the activity increment to prevent overflow.
        self.activity_inc *= VSIDS_RESCALE_FACTOR;

        // Create a new heap with the rescaled scores.
        let mut score_entries: Vec<ScoreEntry> = Vec::with_capacity(self.scores.len());
        for (lit_idx, &score) in self.scores.iter().enumerate() {
            score_entries.push(ScoreEntry {
                score: OrderedFloat(score),
                lit_idx,
            });
        }
        self.heap = BinaryHeap::from(score_entries);
    }
}

/// `VariableSelection` trait implementation for the VSIDS heap.
impl<L: Literal> VariableSelection<L> for VsidsHeap {
    /// Creates a new instance of the VSIDS heap.
    /// Initialises the scores to zero and the activity increment to 1.0.
    fn new<C: AsRef<[L]>>(num_vars: usize, _: &[L], _: &[C]) -> Self {
        let scores = vec![0.0; num_vars * 2];
        let mut score_entries: Vec<ScoreEntry> = Vec::with_capacity(scores.len());
        for (lit_idx, &score) in scores.iter().enumerate() {
            score_entries.push(ScoreEntry {
                score: OrderedFloat(score),
                lit_idx,
            });
        }
        let heap = BinaryHeap::from(score_entries);

        Self {
            scores,
            activity_inc: 1.0,
            heap,
            num_decisions: 0,
        }
    }

    /// Picks a variable based on the current assignment.
    /// Pops from the heap until it finds a variable that is unassigned in the assignment.
    /// Theoretically, this should be a constant time operation, but in practice it is O(log n) due to the heap operations.
    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        while let Some(entry) = self.heap.pop() {
            let current_score = unsafe { *self.scores.get_unchecked(entry.lit_idx) };

            if entry.score != OrderedFloat(current_score) {
                continue;
            }

            if assignment[entry.lit_idx / 2].is_unassigned() {
                self.num_decisions += 1;
                return Some(L::from_index(entry.lit_idx));
            }
        }

        None
    }

    /// Bumps the activity of the given variables.
    fn bumps<T: IntoIterator<Item = L>>(&mut self, vars: T) {
        for i in vars {
            self.bump_internal(i.index());
        }
    }

    /// Decays the activity of the variables.
    /// Instead of decaying the scores directly, we make new assignments to the scores
    /// more important by increasing the activity increment.
    /// If the activity increment exceeds the threshold, we rescale the scores.
    /// Generally, this is a constant time operation, but in practice it is O(n) due to the rescaling.
    fn decay(&mut self, decay: f64) {
        self.activity_inc /= decay;

        if self.activity_inc > VSIDS_RESCALE_THRESHOLD {
            self.rescale_scores();
        }
    }

    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

/// A structure representing the VSIDS variable selection strategy, without the use of a max heap.
///
/// Early exit is a compile-time constant that determines whether to exit early when the score exceeds a threshold.
/// In theory this should be a good idea, but it seems for certain 3-SAT instances it causes the
/// solver to hang.
#[derive(Debug, Clone, PartialEq, Default, PartialOrd)]
pub struct Vsids<const EARLY_EXIT: bool = false> {
    scores: Vec<f64>,
    activity_inc: f64,
    num_vars: usize,
    num_decisions: usize,
}

/// `Index` trait implementation for the VSIDS variable selection strategy.
/// Allows for indexing into the scores vector.
///
/// # Safety
/// Should only be used internally and with care due to the unchecked indexing.
impl<const E: bool> Index<usize> for Vsids<E> {
    type Output = f64;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.scores.get_unchecked(index) }
    }
}

/// `IndexMut` trait implementation for the VSIDS variable selection strategy.
/// Allows for mutable indexing into the scores vector.
///
/// # Safety
/// Again, should only be used internally and with care due to the unchecked indexing.
impl<const E: bool> IndexMut<usize> for Vsids<E> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.scores.get_unchecked_mut(index) }
    }
}

/// `Vsids` implementation.
/// Internal method for bumping the activity of a variable.
impl<const E: bool> Vsids<E> {
    /// Bumps the activity of a variable at the given index.
    /// Very simple bumping function, just adds the activity increment to the score.
    /// I suppose a concern is that this could cause overflow, but we handle that in the decay function.
    fn bump(&mut self, i: impl Literal) {
        self[i.index()] += self.activity_inc;
    }
}

/// `VariableSelection` trait implementation for the VSIDS variable selection strategy.
impl<L: Literal, const E: bool> VariableSelection<L> for Vsids<E> {
    #[must_use]
    /// Creates a new instance of the VSIDS variable selection strategy.
    fn new<C: AsRef<[L]>>(num_vars: usize, _: &[L], _: &[C]) -> Self {
        Self {
            scores: vec![0.0; num_vars * 2],
            activity_inc: 1.0,
            num_vars,
            num_decisions: 0,
        }
    }

    /// Picks a variable based on the current assignment.
    /// Simple iteration over the scores vector, looking for the maximum score.
    /// If the early exit flag is set, we exit early if the score exceeds the threshold.
    /// O(N)
    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        let mut max_score = f64::MIN;
        let mut max = None;

        for (i, &v) in self.scores.iter().enumerate() {
            let lit = L::from_index(i);
            if v > max_score && assignment[lit.variable() as usize].is_unassigned() {
                max = Some(lit);
                max_score = v;

                if E && v > self.activity_inc * 5.0 {
                    break;
                }
            }
        }

        if max.is_some() {
            self.num_decisions += 1;
        }

        max
    }

    /// Bumps the activity of the given variables.
    fn bumps<T: IntoIterator<Item = L>>(&mut self, vars: T) {
        for i in vars {
            self.bump(i);
        }
    }

    /// Decays the activity of the variables.
    /// Instead of decaying the scores directly, we make new assignments to the scores
    /// more important by increasing the activity increment.
    fn decay(&mut self, decay: f64) {
        self.activity_inc /= decay;

        // If the activity increment exceeds the threshold, we rescale the scores.
        // Prevents overflow
        if self.activity_inc > VSIDS_RESCALE_THRESHOLD {
            self.scores
                .iter_mut()
                .for_each(|s| *s *= VSIDS_RESCALE_FACTOR);
            self.activity_inc = VSIDS_RESCALE_FACTOR;
        }
    }

    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

/// A structure representing a fixed order variable selection strategy.
/// This structure returns the next first unassigned variable in the order of the input
/// variables, in a random polarity.
///
/// This should be integrated with a phase selector to determine the polarity.
#[derive(Debug, Clone, Default)]
pub struct FixedOrder {
    var_count: usize,
    rand: RefCell<Rng>,
    num_decisions: usize,
}

impl<L: Literal> VariableSelection<L> for FixedOrder {
    fn new<C: AsRef<[L]>>(num_vars: usize, _: &[L], _: &[C]) -> Self {
        Self {
            var_count: num_vars,
            rand: RefCell::new(Rng::with_seed(0)),
            num_decisions: 0,
        }
    }

    /// Picks a variable based on the current assignment.
    /// Iterates over the variables in order, looking for the first unassigned variable.
    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        #![allow(clippy::cast_possible_truncation)]
        (1..self.var_count as u32).find_map(|v| {
            if assignment[v as usize].is_unassigned() {
                let mut rng = self.rand.borrow_mut();
                let polarity = rng.bool();
                let lit = L::new(v, polarity);
                self.num_decisions += 1;
                Some(lit)
            } else {
                None
            }
        })
    }

    /// NO-OP
    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    /// NO-OP
    fn decay(&mut self, _: f64) {}

    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

/// A structure representing a random order variable selection strategy.
/// This structure returns the next first unassigned variable in a random order.
#[derive(Debug, Clone, Default)]
pub struct RandomOrder {
    rand: RefCell<Rng>,
    vars: Vec<usize>,
    num_decisions: usize,
}

/// `VariableSelection` trait implementation for the random order variable selection strategy.
impl<L: Literal> VariableSelection<L> for RandomOrder {
    fn new<C: AsRef<[L]>>(num_vars: usize, _: &[L], _: &[C]) -> Self {
        let mut rand = Rng::with_seed(0);
        let mut indices: Vec<usize> = (1..num_vars).collect();
        rand.shuffle(indices.as_mut_slice());
        
        Self {
            vars: indices,
            rand: RefCell::new(Rng::new()),
            num_decisions: 0,
        }
    }

    /// Picks a variable based on the current assignment.
    /// Shuffles the variables and iterates over them, looking for the first unassigned variable.
    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        #![allow(clippy::cast_possible_truncation)]

        let mut rng = self.rand.borrow_mut();
        
        for i in &self.vars {
            if assignment[*i].is_unassigned() {
                let polarity = rng.bool();
                self.num_decisions += 1;
                return Some(L::new(*i as u32, polarity));
            }
        }
        None
    }

    /// NO-OP
    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    /// NO-OP
    fn decay(&mut self, _: f64) {}

    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

#[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
fn jw_weight(clause_len: usize) -> f64 {
    if clause_len == 0 {
        0.0
    } else {
        2.0_f64.powi(-(clause_len as i32))
    }
}

fn init_jw_scores<L: Literal, C: AsRef<[L]>>(num_vars: usize, clauses: &[C]) -> Vec<f64> {
    let mut scores = vec![0.0; num_vars * 2];
    for clause in clauses {
        let len = clause.as_ref().len();
        let weight = jw_weight(len);
        for &lit in clause.as_ref() {
            scores[lit.index()] += weight;
        }
    }
    scores
}

#[derive(Debug, Clone, Default)]
pub struct JeroslowWangOneSided {
    scores: Vec<f64>,
    rand: RefCell<Rng>,
    num_decisions: usize,
}

impl<L: Literal> VariableSelection<L> for JeroslowWangOneSided {
    fn new<C: AsRef<[L]>>(num_vars: usize, _: &[L], clauses: &[C]) -> Self {
        let scores = init_jw_scores(num_vars, clauses);

        Self {
            scores,
            rand: RefCell::new(Rng::with_seed(0)),
            num_decisions: 0,
        }
    }

    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        let mut max_score = f64::MIN;
        let mut best_lit = None;

        for i in 0..self.scores.len() {
            let lit = L::from_index(i);
            if assignment[lit.variable() as usize].is_unassigned() {
                let score = self.scores[i];
                if score > max_score {
                    max_score = score;
                    best_lit = Some(lit);
                }
            }
        }

        best_lit.map(|lit| {
            self.num_decisions += 1;

            if self.rand.borrow_mut().f64() < 0.1 {
                lit.negated()
            } else {
                lit
            }
        })
    }

    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    fn decay(&mut self, _: f64) {}

    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

#[derive(Debug, Clone, Default)]
pub struct JeroslowWangTwoSided {
    scores: Vec<f64>,
    num_vars: usize,
    rand: RefCell<Rng>,
    num_decisions: usize,
}

impl<L: Literal> VariableSelection<L> for JeroslowWangTwoSided {
    fn new<C: AsRef<[L]>>(num_vars: usize, _: &[L], clauses: &[C]) -> Self {
        let scores = init_jw_scores(num_vars, clauses);

        Self {
            scores,
            num_vars,
            rand: RefCell::new(Rng::with_seed(0)),
            num_decisions: 0,
        }
    }

    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        let mut max_score = f64::MIN;
        let mut best_lit = None;

        for i in 0..self.num_vars {
            if assignment[i].is_unassigned() {
                let neg_lit_idx = 2 * i;
                let pos_lit_idx = 2 * i + 1;

                let combined_score = self.scores[neg_lit_idx] + self.scores[pos_lit_idx];

                if combined_score > max_score {
                    max_score = combined_score;
                    best_lit = Some(i);
                }
            }
        }
        best_lit
            .map(|v_dix| {
                let ng_lit_idx = 2 * v_dix;
                let pos_lit_idx = 2 * v_dix + 1;

                let neg_score = self.scores[ng_lit_idx];
                let pos_score = self.scores[pos_lit_idx];

                if neg_score > pos_score {
                    L::from_index(ng_lit_idx)
                } else if neg_score < pos_score {
                    L::from_index(pos_lit_idx)
                } else {
                    let mut rng = self.rand.borrow_mut();
                    if rng.bool() {
                        L::from_index(ng_lit_idx)
                    } else {
                        L::from_index(pos_lit_idx)
                    }
                }
            })
            .map(|lit| {
                self.num_decisions += 1;
                if self.rand.borrow_mut().f64() < 0.1 {
                    lit.negated()
                } else {
                    lit
                }
            })
    }

    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    fn decay(&mut self, _: f64) {}

    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

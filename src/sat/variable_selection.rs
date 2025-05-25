#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
//! Defines variable selection strategies (decision heuristics) for SAT solvers.
//!
//! The variable selection strategy (often called the decision heuristic) determines
//! which unassigned variable to pick next and what truth value to assign to it
//! during the search process. A good heuristic can significantly impact solver performance.
//!
//! This module provides:
//! - The `VariableSelection` trait, defining a common interface for these strategies.
//! - Several concrete implementations:
//!   - `VsidsHeap`: Implements VSIDS (Variable State Independent Decaying Sum) using a binary heap
//!     to efficiently find the variable with the highest activity score.
//!   - `Vsids`: A simpler VSIDS implementation that iterates through scores without a heap.
//!   - `FixedOrder`: Selects variables in a fixed, predefined order (e.g. by variable index).
//!   - `RandomOrder`: Selects variables in a (shuffled) random order.
//!   - `JeroslowWangOneSided`: Implements the Jeroslow-Wang heuristic (one-sided version),
//!     which scores literals based on their occurrence in short clauses.
//!   - `JeroslowWangTwoSided`: A two-sided version of the Jeroslow-Wang heuristic.

use crate::sat::assignment::Assignment;
use crate::sat::literal::Literal;
use fastrand::Rng;
use ordered_float::OrderedFloat;
use std::cell::RefCell;
use std::collections::BinaryHeap;
use std::fmt::Debug;
use std::ops::{Index, IndexMut};

/// Trait defining the interface for variable selection strategies.
///
/// Implementors of this trait decide which unassigned variable to choose next for a decision
/// and, implicitly or explicitly, which polarity to assign to it.
///
/// # Type Parameters
///
/// * `L`: The `Literal` type used by the solver.
pub trait VariableSelection<L: Literal>: Debug + Clone {
    /// Creates a new instance of the variable selection strategy.
    ///
    /// # Parameters
    ///
    /// * `num_vars`: The total number of variables in the SAT problem.
    /// * `vars`: A slice of all literals (often used for initial setup, though not all strategies use it).
    /// * `clauses`: A slice of clauses in the SAT problem. Some strategies use this to
    ///   initialise scores.
    fn new<C: AsRef<[L]>>(num_vars: usize, vars: &[L], clauses: &[C]) -> Self;

    /// Picks an unassigned variable for the next decision.
    ///
    /// Returns `Some(L)` with the chosen literal (variable and its assigned polarity)
    /// if an unassigned variable can be found. Returns `None` if all variables
    /// relevant to the strategy are assigned.
    ///
    /// # Parameters
    ///
    /// * `assignment`: The current state of variable assignments in the solver.
    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L>;

    /// Increases the activity score of the specified variables.
    ///
    /// This is called when a conflict is analysed, and the variables
    /// involved in the conflict (or the learned clause) are "rewarded".
    ///
    /// # Parameters
    ///
    /// * `vars`: An iterator over literals whose activity should be bumped.
    fn bumps<T: IntoIterator<Item = L>>(&mut self, vars: T);

    /// Decays the activity scores of all variables.
    ///
    /// This is periodically called to give more weight to recently active variables.
    /// The exact mechanism can vary (e.g. multiplying all scores by a factor,
    /// or increasing an activity increment).
    ///
    /// # Parameters
    ///
    /// * `decay`: The decay factor. The interpretation of this factor depends on the specific strategy.
    ///   For VSIDS-like strategies, it's typically a value slightly less than 1 (e.g. 0.95),
    ///   and `activity_inc` is divided by this factor.
    fn decay(&mut self, decay: f64);

    /// Returns the number of decisions made by this strategy.
    fn decisions(&self) -> usize;
}
/// A structure representing a score entry in the VSIDS heap.
///
/// This struct is used to store a variable's (literal's) activity score along with its index,
/// primarily for use in a `BinaryHeap`. `OrderedFloat` is used for the score to ensure
/// proper ordering in the heap, as `f64` itself does not implement `Ord`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ScoreEntry {
    /// The activity score of the literal.
    /// `OrderedFloat` is used to ensure that `f64` values can be correctly ordered in the `BinaryHeap`,
    /// as `f64` itself does not implement `Ord` due to NaN.
    score: OrderedFloat<f64>,
    /// The index of the literal (as returned by `Literal::index()`).
    lit_idx: usize,
}

/// A constant for the VSIDS rescale threshold.
/// When the activity increment (`activity_inc`) in VSIDS-like heuristics exceeds this value,
/// scores are rescaled to prevent floating-point overflow and maintain numerical stability.
const VSIDS_RESCALE_THRESHOLD: f64 = 1e100;
/// A constant for the VSIDS rescale factor.
/// Scores are multiplied by this factor during rescaling to bring them back into a manageable range.
const VSIDS_RESCALE_FACTOR: f64 = 1e-100;

/// A constant for the decay factor used in VSIDS-like heuristics.
pub const VSIDS_DECAY_FACTOR: f64 = 0.95;

/// A VSIDS (Variable State Independent Decaying Sum) implementation using a binary heap.
///
/// This strategy maintains an activity score for each literal. Variables involved in recent
/// conflicts get their scores "bumped". Periodically, all scores "decay".
/// The `BinaryHeap` is used to efficiently find the unassigned literal with the highest activity score.
/// This implementation aims for `O(log N)` pick operations on average, where N is the number of variables.
#[derive(Debug, Clone)]
pub struct VsidsHeap {
    /// Stores the current activity scores for each literal. The index corresponds to `Literal::index()`.
    /// For a variable `v`, `scores[2*v]` might be negative literal and `scores[2*v+1]` positive,
    /// or based on `Literal::index()` directly.
    scores: Vec<f64>,
    /// The amount by which a literal's score is incremented during a "bump".
    /// This value itself is adjusted during decay operations (typically increased, effectively
    /// making newer bumps more significant relative to older scores before rescaling).
    activity_inc: f64,
    /// A max-heap storing `ScoreEntry` items. It allows efficient retrieval of the literal
    /// with the highest current activity score. Entries in the heap might be stale;
    /// they are validated against the `scores` vector upon extraction.
    heap: BinaryHeap<ScoreEntry>,
    /// Counter for the number of decisions made by this strategy.
    num_decisions: usize,
}

/// `Index` trait implementation for the VSIDS heap.
/// Allows for indexing into the scores vector using a `usize` that typically corresponds
/// to `Literal::index()`.
///
/// # Safety
/// This implementation uses `get_unchecked` for performance
impl Index<usize> for VsidsHeap {
    type Output = f64;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.scores.get_unchecked(index) }
    }
}

/// `IndexMut` trait implementation for the VSIDS heap.
/// Allows for mutable indexing into the scores vector using a `usize` that typically
/// corresponds to `Literal::index()`.
///
/// # Safety
/// Similar to the `Index` implementation, this uses `get_unchecked_mut`.
impl IndexMut<usize> for VsidsHeap {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.scores.get_unchecked_mut(index) }
    }
}

impl VsidsHeap {
    /// Bumps the activity of a literal at the given index and updates the heap.
    ///
    /// The score in the `scores` vector is updated by adding `activity_inc`.
    /// A new `ScoreEntry` reflecting this updated score is pushed onto the heap.
    /// Old entries for the same literal with outdated scores are not immediately
    /// removed from the heap; they are filtered out during `pick` when their score
    /// doesn't match the `scores` vector, or eventually cleared during `rescale_scores`.
    fn bump_internal(&mut self, lit_idx: usize) {
        let score_ref = unsafe { self.scores.get_unchecked_mut(lit_idx) };
        *score_ref += self.activity_inc;
        let new_score = *score_ref;

        // push the new score entry into the heap.
        // at this point we don't need to remove the old entry, that is handled when rescaling.
        self.heap.push(ScoreEntry {
            score: OrderedFloat(new_score),
            lit_idx,
        });
    }

    /// Rescales all activity scores and the activity increment.
    ///
    /// This operation is performed when `activity_inc` grows too large (exceeds
    /// `VSIDS_RESCALE_THRESHOLD`). All scores in the `scores` vector are multiplied
    /// by `VSIDS_RESCALE_FACTOR` (a value less than 1) to bring them into a smaller range,
    /// preventing floating-point overflow. The `activity_inc` is also rescaled.
    ///
    /// After rescaling scores, the `heap` is rebuilt from the `scores` vector. This ensures
    /// that the heap accurately reflects the new scores and also cleans up any stale
    /// `ScoreEntry` items (those whose scores in the heap did not match the `scores` vector).
    fn rescale_scores(&mut self) {
        // rescale the scores to prevent overflow
        self.scores
            .iter_mut()
            .for_each(|s| *s *= VSIDS_RESCALE_FACTOR);
        // rescale the activity increment to prevent overflow
        self.activity_inc *= VSIDS_RESCALE_FACTOR;

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
    /// Creates a new instance of the `VsidsHeap` strategy.
    ///
    /// Initialises scores for all possible literals (2 * `num_vars`) to zero.
    /// The `activity_inc` is initialised to 1.0.
    /// The heap is populated with initial zero scores for all literals.
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

    /// Picks an unassigned variable with the highest activity score.
    ///
    /// It repeatedly pops from the `heap` until it finds a `ScoreEntry` whose
    /// corresponding variable is unassigned and whose score matches the current score
    /// in the `scores` vector (to filter out stale entries).
    ///
    /// The complexity is typically `O(log N)` for heap pop, but can be higher if many
    /// stale entries need to be processed.
    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        while let Some(entry) = self.heap.pop() {
            let current_score = unsafe { *self.scores.get_unchecked(entry.lit_idx) };

            if entry.score != OrderedFloat(current_score) {
                continue;
            }

            if assignment[entry.lit_idx / 2].is_unassigned() {
                self.num_decisions = self.num_decisions.wrapping_add(1);
                return Some(L::from_index(entry.lit_idx));
            }
        }

        None
    }

    /// Bumps the activity scores of the specified literals.
    ///
    /// For each literal in `vars`, its score is incremented by `activity_inc`,
    /// and the heap is updated accordingly via `bump_internal`.
    fn bumps<T: IntoIterator<Item = L>>(&mut self, vars: T) {
        for i in vars {
            self.bump_internal(i.index());
        }
    }

    /// Decays the activity scores.
    ///
    /// In this VSIDS implementation, scores are not directly decayed. Instead,
    /// `activity_inc` is divided by the `decay` factor (typically `0 < decay < 1`,
    /// e.g. 0.95, so `activity_inc` effectively increases). This gives more weight
    /// to variables involved in more recent conflicts.
    ///
    /// If `activity_inc` exceeds `VSIDS_RESCALE_THRESHOLD`, all scores and
    /// `activity_inc` are rescaled by multiplying with `VSIDS_RESCALE_FACTOR`
    /// to prevent overflow and maintain precision. This rescaling step involves
    /// rebuilding the heap, which can be an `O(N)` operation.
    fn decay(&mut self, decay: f64) {
        self.activity_inc /= decay;

        if self.activity_inc > VSIDS_RESCALE_THRESHOLD {
            self.rescale_scores();
        }
    }

    /// Returns the total number of decisions made by this strategy instance.
    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

/// A VSIDS (Variable State Independent Decaying Sum) implementation without a binary heap.
///
/// This strategy maintains an activity score for each literal. When picking a variable,
/// it iterates through all literals to find the unassigned one with the highest score.
/// This makes the `pick` operation `O(N)` where N is the number of variables.
///
/// `EARLY_EXIT` is a compile-time constant. If `true`, the `pick` operation may
/// exit early if a literal with a sufficiently high score is found, potentially
/// saving computation but possibly leading to suboptimal choices in some cases.
#[derive(Debug, Clone, PartialEq, Default, PartialOrd)]
pub struct Vsids<const EARLY_EXIT: bool = false> {
    /// Stores the current activity scores for each literal.
    /// The index corresponds to `Literal::index()`.
    scores: Vec<f64>,
    /// The amount by which a literal's score is incremented during a "bump".
    /// Adjusted during decay operations.
    activity_inc: f64,
    /// The total number of variables in the problem. Used to iterate appropriately.
    num_vars: usize,
    /// Counter for the number of decisions made by this strategy.
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
impl<const E: bool> Vsids<E> {
    /// Bumps the activity of a variable at the given literal's index.
    /// The score of the literal `i` is incremented by `activity_inc`.
    /// This method is internal to the `Vsids` strategy.
    fn bump(&mut self, i: impl Literal) {
        self[i.index()] += self.activity_inc;
    }
}

/// `VariableSelection` trait implementation for the VSIDS variable selection strategy.
impl<L: Literal, const E: bool> VariableSelection<L> for Vsids<E> {
    /// Creates a new instance of the `Vsids` strategy.
    /// Initialises scores for all literals to zero and `activity_inc` to 1.0.
    fn new<C: AsRef<[L]>>(num_vars: usize, _: &[L], _: &[C]) -> Self {
        Self {
            scores: vec![0.0; num_vars * 2], // scores for positive and negative literals
            activity_inc: 1.0,
            num_vars,
            num_decisions: 0,
        }
    }

    /// Picks an unassigned variable with the highest activity score by iterating through all literals.
    ///
    /// This operation is `O(N)` where N is the number of variables.
    /// If `EARLY_EXIT` (compile-time const generic `E`) is true, the iteration
    /// might stop early if a literal's score exceeds `self.activity_inc * 5.0`.
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
            self.num_decisions = self.num_decisions.wrapping_add(1);
        }

        max
    }

    /// Bumps the activity scores of the specified literals.
    /// Each literal's score is incremented by `activity_inc`.
    fn bumps<T: IntoIterator<Item = L>>(&mut self, vars: T) {
        for i in vars {
            self.bump(i);
        }
    }

    /// Decays the activity scores.
    /// Similar to `VsidsHeap`, `activity_inc` is divided by `decay` (effectively increasing it).
    /// If `activity_inc` exceeds `VSIDS_RESCALE_THRESHOLD`, all scores are rescaled by
    /// multiplying with `VSIDS_RESCALE_FACTOR`, and `activity_inc` is also set to
    /// `VSIDS_RESCALE_FACTOR` (note: this differs slightly from `VsidsHeap` which rescales `activity_inc`
    /// by the same factor; here it's reset). This prevents overflow.
    fn decay(&mut self, decay: f64) {
        self.activity_inc /= decay;

        if self.activity_inc > VSIDS_RESCALE_THRESHOLD {
            self.scores
                .iter_mut()
                .for_each(|s| *s *= VSIDS_RESCALE_FACTOR);

            self.activity_inc *= VSIDS_RESCALE_FACTOR;
        }
    }

    /// Returns the total number of decisions made by this strategy instance.
    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

/// A variable selection strategy that picks variables in a fixed, predefined order.
///
/// It iterates through variables by their index (1 to `num_vars - 1`).
/// The first unassigned variable encountered is chosen.
/// The polarity (truth value) assigned to the chosen variable is selected randomly.
///
/// This strategy is simple and deterministic in variable choice (once an order is set)
/// but random in polarity.
#[derive(Debug, Clone, Default)]
pub struct FixedOrder {
    /// The total number of variables in the problem.
    var_count: usize,
    /// Random number generator used for selecting polarity.
    /// `RefCell` is used to allow mutable access to `Rng` in `pick` method,
    /// which takes `&mut self`.
    rand: RefCell<Rng>,
    /// Counter for the number of decisions made by this strategy.
    num_decisions: usize,
}

impl<L: Literal> VariableSelection<L> for FixedOrder {
    /// Creates a new `FixedOrder` strategy.
    /// `num_vars` is the total number of variables.
    /// The random number generator is initialised with a fixed seed (0).
    fn new<C: AsRef<[L]>>(num_vars: usize, _: &[L], _: &[C]) -> Self {
        Self {
            var_count: num_vars,
            rand: RefCell::new(Rng::with_seed(0)), // fixed seed for deterministic behavior
            num_decisions: 0,
        }
    }

    /// Picks the first unassigned variable according to a fixed order (variable index).
    /// Variables are typically checked from index 1 up to `var_count - 1`.
    /// The polarity of the chosen variable is selected randomly.
    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        #![allow(clippy::cast_possible_truncation)]
        (1..self.var_count as u32).find_map(|v| {
            if assignment[v as usize].is_unassigned() {
                let mut rng = self.rand.borrow_mut();
                let polarity = rng.bool();
                let lit = L::new(v, polarity);
                self.num_decisions = self.num_decisions.wrapping_add(1);
                Some(lit)
            } else {
                None
            }
        })
    }

    /// No-op
    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    /// No-op
    fn decay(&mut self, _: f64) {}

    /// Returns the total number of decisions made by this strategy instance.
    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

/// A variable selection strategy that picks variables in a random order.
///
/// On initialisation, it creates a shuffled list of variable indices.
/// When `pick` is called, it iterates through this shuffled list and chooses the
/// first unassigned variable it encounters. The polarity of the chosen variable
/// is selected randomly.
///
/// The initial shuffling makes the order random but fixed for the lifetime of this instance
#[derive(Debug, Clone, Default)]
pub struct RandomOrder {
    /// Random number generator for selecting polarity and initial shuffling.
    /// `RefCell` for mutable access in `pick`.
    rand: RefCell<Rng>,
    /// A list of variable indices, shuffled once at initialisation.
    /// The `pick` method iterates through this list.
    /// Indices stored here are typically 0-indexed if `num_vars` in `new` is count.
    vars: Vec<usize>,
    /// Counter for the number of decisions made by this strategy.
    num_decisions: usize,
}

/// `VariableSelection` trait implementation for the random order variable selection strategy.
impl<L: Literal> VariableSelection<L> for RandomOrder {
    /// Creates a new `RandomOrder` strategy.
    /// `num_vars` is the total number of variables.
    /// It initialises a list of variable indices (e.g. 0 to `num_vars - 1` or 1 to `num_vars`)
    /// and shuffles it using an `Rng` seeded with 0 for deterministic shuffling.
    /// A separate `Rng` (newly created) is stored for random polarity selection.
    fn new<C: AsRef<[L]>>(num_vars: usize, _: &[L], _: &[C]) -> Self {
        let mut shuffle_rng = Rng::with_seed(0);
        let mut indices: Vec<usize> = (0..num_vars).collect();
        shuffle_rng.shuffle(indices.as_mut_slice());

        Self {
            vars: indices,
            rand: RefCell::new(Rng::new()),
            num_decisions: 0,
        }
    }

    /// Picks an unassigned variable from the pre-shuffled list.
    /// Iterates through the `vars` list. The first variable index `i` encountered
    /// for which `assignment[i]` is unassigned is chosen.
    /// Polarity is chosen randomly.
    fn pick<A: Assignment>(&mut self, assignment: &A) -> Option<L> {
        #![allow(clippy::cast_possible_truncation)] 

        let mut rng = self.rand.borrow_mut();

        for &var_idx in &self.vars {
            if assignment[var_idx].is_unassigned() {
                let polarity = rng.bool();
                self.num_decisions = self.num_decisions.wrapping_add(1);
                return Some(L::new(var_idx as u32, polarity));
            }
        }
        None
    }

    /// No-op
    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    /// No-op
    fn decay(&mut self, _: f64) {}

    /// Returns the total number of decisions made by this strategy instance.
    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

/// Calculates the Jeroslow-Wang weight for a clause.
/// The weight is `2^(-clause_len)`. Returns 0.0 if `clause_len` is 0.
///
/// # Parameters
/// * `clause_len`: The length (number of literals) of the clause.
///
/// # Returns
/// The calculated weight as an `f64`.
#[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
fn jw_weight(clause_len: usize) -> f64 {
    if clause_len == 0 {
        0.0
    } else {
        2.0_f64.powi(-(clause_len as i32))
    }
}

/// Initialises scores for Jeroslow-Wang heuristics.
///
/// Iterates through all clauses, calculates the JW weight for each clause,
/// and adds this weight to the score of each literal present in that clause.
/// The scores vector is indexed by `Literal::index()`.
///
/// # Type Parameters
/// * `L`: The `Literal` type.
/// * `C`: A type that can be referenced as a slice of literals `&[L]`, typically a clause.
///
/// # Parameters
/// * `num_vars`: The total number of variables. Scores vector will be `num_vars * 2`.
/// * `clauses`: A slice of clauses to compute initial scores from.
///
/// # Returns
/// A `Vec<f64>` containing the initial scores for each literal.
fn init_jw_scores<L: Literal, C: AsRef<[L]>>(num_vars: usize, clauses: &[C]) -> Vec<f64> {
    let mut scores = vec![0.0; num_vars * 2];
    for clause_ref in clauses {
        let clause = clause_ref.as_ref();
        let len = clause.len();
        let weight = jw_weight(len);
        for &lit in clause {
            scores[lit.index()] += weight;
        }
    }
    scores
}

/// Implements the Jeroslow-Wang heuristic (one-sided version).
///
/// This heuristic scores literals based on their occurrences in clauses,
/// giving higher weight to literals in shorter clauses (specifically, `2^(-clause_length)`).
/// When picking a variable, it chooses the literal (variable and polarity) with the
/// highest score among unassigned literals.
///
/// There's a small chance (10%) that the chosen literal's polarity will be flipped,
/// adding an element of randomness.
#[derive(Debug, Clone, Default)]
pub struct JeroslowWangOneSided {
    /// Stores the Jeroslow-Wang scores for each literal, indexed by `Literal::index()`.
    /// These scores are typically initialised based on clause lengths and do not decay.
    scores: Vec<f64>,
    /// Random number generator, used for the 10% chance of flipping polarity.
    rand: RefCell<Rng>,
    /// Counter for the number of decisions made by this strategy.
    num_decisions: usize,
}

impl<L: Literal> VariableSelection<L> for JeroslowWangOneSided {
    /// Creates a new `JeroslowWangOneSided` strategy.
    /// Initialises scores using `init_jw_scores` based on the provided clauses.
    /// The random number generator is seeded with 0.
    fn new<C: AsRef<[L]>>(num_vars: usize, _: &[L], clauses: &[C]) -> Self {
        let scores = init_jw_scores(num_vars, clauses);

        Self {
            scores,
            rand: RefCell::new(Rng::with_seed(0)),
            num_decisions: 0,
        }
    }

    /// Picks an unassigned literal with the highest Jeroslow-Wang score.
    /// It iterates through all literals, finds the unassigned one with the maximum score.
    /// There is a 10% chance the polarity of this chosen literal will be flipped.
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
            self.num_decisions = self.num_decisions.wrapping_add(1);

            if self.rand.borrow_mut().f64() < 0.1 {
                lit.negated()
            } else {
                lit
            }
        })
    }

    /// JW scores are static, based on initial clause structure.
    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    /// JW scores are static.
    fn decay(&mut self, _: f64) {}

    /// Returns the total number of decisions made by this strategy instance.
    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

/// Implements a two-sided version of the Jeroslow-Wang heuristic.
///
/// This heuristic first selects a variable based on the sum of JW scores for its
/// positive and negative literals (`score(v) = JW(v) + JW(-v)`).
/// Once a variable is chosen, it picks the polarity (positive or negative)
/// that has the higher individual JW score. If scores are equal, polarity is chosen randomly.
///
/// Similar to the one-sided version, there's a small chance (10%) that the final
/// chosen literal's polarity will be flipped.
#[derive(Debug, Clone, Default)]
pub struct JeroslowWangTwoSided {
    /// Stores the Jeroslow-Wang scores for each literal, indexed by `Literal::index()`.
    scores: Vec<f64>,
    /// The total number of variables in the problem.
    num_vars: usize,
    /// Random number generator, used for tie-breaking polarity and the 10% polarity flip.
    rand: RefCell<Rng>,
    /// Counter for the number of decisions made by this strategy.
    num_decisions: usize,
}

impl<L: Literal> VariableSelection<L> for JeroslowWangTwoSided {
    /// Creates a new `JeroslowWangTwoSided` strategy.
    /// Initialises scores using `init_jw_scores`.
    /// The random number generator is seeded with 0.
    fn new<C: AsRef<[L]>>(num_vars: usize, _: &[L], clauses: &[C]) -> Self {
        let scores = init_jw_scores(num_vars, clauses);

        Self {
            scores,
            num_vars,
            rand: RefCell::new(Rng::with_seed(0)),
            num_decisions: 0,
        }
    }

    /// Picks a variable and its polarity using the two-sided Jeroslow-Wang heuristic.
    /// 1. Finds the unassigned variable `v` maximising `JW(v_pos) + JW(v_neg)`.
    /// 2. For the chosen `v`, selects the literal (positive or negative) with the higher JW score.
    ///    Ties are broken randomly.
    /// 3. There is a 10% chance the polarity of this final literal is flipped.
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
                self.num_decisions = self.num_decisions.wrapping_add(1);
                if self.rand.borrow_mut().f64() < 0.1 {
                    lit.negated()
                } else {
                    lit
                }
            })
    }

    /// Bumps scores. NO-OP for `JeroslowWangTwoSided`.
    /// JW scores are static.
    fn bumps<T: IntoIterator<Item = L>>(&mut self, _: T) {}

    /// Decays scores. NO-OP for `JeroslowWangTwoSided`.
    /// JW scores are static.
    fn decay(&mut self, _: f64) {}

    /// Returns the total number of decisions made by this strategy instance.
    fn decisions(&self) -> usize {
        self.num_decisions
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::assignment::VecAssignment;
    use crate::sat::clause::Clause;
    use crate::sat::literal::{PackedLiteral, Variable};
    use smallvec::SmallVec;

    type TestLiteral = PackedLiteral;
    type TestClause = Clause<TestLiteral, SmallVec<[TestLiteral; 8]>>;
    type TestAssignment = VecAssignment;

    fn lit(val: i32) -> TestLiteral {
        TestLiteral::from_i32(val)
    }
    fn clause(lits_dimacs: &[i32]) -> TestClause {
        lits_dimacs.iter().map(|&x| lit(x)).collect()
    }

    fn test_selector_behavior<VS: VariableSelection<TestLiteral>>(
        mut selector: VS,
        num_vars_for_assignment: usize,
        expected_decisions_if_all_picked: usize,
    ) {
        let mut assignment = TestAssignment::new(num_vars_for_assignment);
        let mut picked_literals = Vec::new();

        for _ in 0..num_vars_for_assignment {
            if let Some(picked_lit) = selector.pick(&assignment) {
                assert!(
                    assignment[picked_lit.variable() as usize].is_unassigned(),
                    "Picked an already assigned variable's literal form. Var: {}",
                    picked_lit.variable()
                );
                assignment.assign(picked_lit);
                picked_literals.push(picked_lit);
            } else {
                break;
            }
        }

        assert_eq!(
            picked_literals.len(),
            expected_decisions_if_all_picked,
            "Number of picked literals/decisions mismatch"
        );
        assert_eq!(
            selector.decisions(),
            expected_decisions_if_all_picked,
            "Internal decision count mismatch"
        );

        let picked_vars_set: std::collections::HashSet<Variable> =
            picked_literals.iter().map(|l| l.variable()).collect();
        assert_eq!(
            picked_vars_set.len(),
            picked_literals.len(),
            "Picked variables are not unique"
        );

        selector.bumps(picked_literals.clone());
        selector.decay(0.95);
    }

    const NUM_VARS_TEST: usize = 5;
    const EMPTY_LITS_SLICE: [TestLiteral; 0] = [];
    const EMPTY_CLAUSES_SLICE: [TestClause; 0] = [];

    #[test]
    fn test_vsids_heap() {
        let selector = VsidsHeap::new(NUM_VARS_TEST, &EMPTY_LITS_SLICE, &EMPTY_CLAUSES_SLICE);
        test_selector_behavior(selector, NUM_VARS_TEST, NUM_VARS_TEST);
    }

    #[test]
    fn test_vsids_no_heap() {
        let selector = Vsids::<false>::new(NUM_VARS_TEST, &EMPTY_LITS_SLICE, &EMPTY_CLAUSES_SLICE);
        test_selector_behavior(selector, NUM_VARS_TEST, NUM_VARS_TEST);
    }

    #[test]
    fn test_vsids_no_heap_early_exit() {
        let selector = Vsids::<true>::new(NUM_VARS_TEST, &EMPTY_LITS_SLICE, &EMPTY_CLAUSES_SLICE);
        test_selector_behavior(selector, NUM_VARS_TEST, NUM_VARS_TEST);
    }

    // #[test]
    // fn test_fixed_order() {
    //     let selector = FixedOrder::new(NUM_VARS_TEST, &EMPTY_LITS_SLICE, &EMPTY_CLAUSES_SLICE);
    //     test_selector_behavior(selector, NUM_VARS_TEST, NUM_VARS_TEST);
    // }

    #[test]
    fn test_random_order() {
        let selector = RandomOrder::new(NUM_VARS_TEST, &EMPTY_LITS_SLICE, &EMPTY_CLAUSES_SLICE);
        test_selector_behavior(selector, NUM_VARS_TEST, NUM_VARS_TEST);
    }

    // #[test]
    // fn test_jeroslow_wang_one_sided() {
    //     let clauses = vec![clause(&[1, 2]), clause(&[-1, 3]), clause(&[2])];
    //     let num_problem_vars = 3;
    //     let selector = JeroslowWangOneSided::new(num_problem_vars , &EMPTY_LITS_SLICE, &clauses);
    //     test_selector_behavior(selector, num_problem_vars, num_problem_vars);
    // }
    // 
    // #[test]
    // fn test_jeroslow_wang_two_sided() {
    //     let clauses = vec![clause(&[1, 2]), clause(&[-1, 3]), clause(&[2])];
    //     let num_problem_vars = 3;
    //     let selector = JeroslowWangTwoSided::new(num_problem_vars + 1, &EMPTY_LITS_SLICE, &clauses);
    //     test_selector_behavior(selector, num_problem_vars, num_problem_vars);
    // }

    #[test]
    fn test_vsids_heap_bumping_and_decay() {
        let mut selector: VsidsHeap = VariableSelection::<TestLiteral>::new(
            NUM_VARS_TEST,
            &EMPTY_LITS_SLICE,
            &EMPTY_CLAUSES_SLICE,
        );
        let mut assignment = TestAssignment::new(NUM_VARS_TEST);

        let lit1_opt = selector.pick(&assignment);
        assert!(lit1_opt.is_some(), "Should be able to pick a literal");
        let lit1: TestLiteral = lit1_opt.unwrap();
        assignment.assign(lit1);
        let lit1_score_before_bump = selector.scores[lit1.index()];

        selector.bumps(std::iter::once(lit1));
        let lit1_score_after_bump = selector.scores[lit1.index()];
        assert!(
            lit1_score_after_bump > lit1_score_before_bump || selector.activity_inc == 0.0,
            "Score should increase after bump"
        );
        assert!(
            (lit1_score_after_bump - (lit1_score_before_bump + selector.activity_inc)).abs() < 1e-9,
            "Score did not increase by activity_inc"
        );

        let _lit2_opt: Option<TestLiteral> = selector.pick(&assignment);
    }

    #[test]
    fn test_vsids_heap_rescaling() {
        let mut selector: VsidsHeap =
            VariableSelection::<PackedLiteral>::new(1, &EMPTY_LITS_SLICE, &EMPTY_CLAUSES_SLICE);
        selector.activity_inc = VSIDS_RESCALE_THRESHOLD * 2.0;

        let lit_to_bump = PackedLiteral::new(0, true);
        assert_eq!(selector.scores[lit_to_bump.index()], 0.0);

        selector.bumps(std::iter::once(lit_to_bump));
        let score_before_decay_and_rescale = selector.scores[lit_to_bump.index()];
        assert_eq!(
            score_before_decay_and_rescale,
            VSIDS_RESCALE_THRESHOLD * 2.0
        );

        <VsidsHeap as VariableSelection<TestLiteral>>::decay(&mut selector, 2.0);
        assert!((selector.activity_inc - VSIDS_RESCALE_THRESHOLD).abs() < 1e-9);
        assert_eq!(
            selector.scores[lit_to_bump.index()],
            score_before_decay_and_rescale,
            "Scores should not change on this decay"
        );

        selector.activity_inc = VSIDS_RESCALE_THRESHOLD * 10.0;
        <VsidsHeap as VariableSelection<TestLiteral>>::decay(&mut selector, 2.0);

        let score_after_rescale = selector.scores[lit_to_bump.index()];
        let activity_inc_after_rescale = selector.activity_inc;

        let expected_rescaled_score = score_before_decay_and_rescale * VSIDS_RESCALE_FACTOR;
        assert!(
            (score_after_rescale - expected_rescaled_score).abs() < 1e-9,
            "Score not rescaled correctly"
        );

        let expected_rescaled_activity_inc = (VSIDS_RESCALE_THRESHOLD * 5.0) * VSIDS_RESCALE_FACTOR;
        assert!(
            (activity_inc_after_rescale - expected_rescaled_activity_inc).abs() < 1e-9,
            "Activity increment not rescaled correctly"
        );
        assert!(
            activity_inc_after_rescale < VSIDS_RESCALE_THRESHOLD,
            "Activity increment should be below threshold after rescale"
        );
    }
}

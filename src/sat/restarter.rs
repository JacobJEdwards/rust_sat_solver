//! Defines restart strategies for SAT solvers.
//!
//! Restart strategies determine when a SAT solver should abandon its current search path
//! and restart the search from the root, typically with different heuristics or a randomized
//! variable selection order. Restarts can help escape "stuck" regions of the search space
//! and improve overall solver performance, especially on hard instances.
//!
//! This module provides:
//! - The `Restarter` trait, defining a common interface for restart strategies.
//! - Several concrete implementations:
//!   - `Luby`: Implements a restart strategy based on the Luby sequence, which provides
//!     a theoretically optimal restart schedule under certain assumptions. The interval
//!     between restarts increases according to the Luby sequence.
//!   - `Geometric`: Implements a geometric restart strategy where the interval between
//!     restarts is multiplied by a constant factor `N` after each restart.
//!   - `Fixed`: Implements a fixed interval restart strategy where restarts occur
//!     every `N` conflicts (or other units, depending on when `should_restart` is called).
//!   - `Linear`: Implements a linear restart strategy where the interval between
//!     restarts increases by a fixed amount `N` after each restart.
//!   - `Never`: A strategy that never triggers a restart.

use fastrand::usize;
use std::fmt::Debug;

/// Trait defining the interface for restart strategies.
///
/// Implementors of this trait determine when the solver should perform a restart.
/// The decision is typically based on a counter, often representing the number of conflicts
/// encountered since the last restart.
pub trait Restarter: Debug + Clone {
    /// Creates a new instance of the restart strategy, initialized to its starting state.
    fn new() -> Self;

    /// Returns the number of conflicts (or other units) remaining until the next restart.
    /// When this count reaches zero, a restart should occur.
    fn restarts_in(&self) -> usize;

    /// Decrements the count of conflicts (or units) remaining until the next restart.
    /// This is typically called after each conflict in the solver.
    fn increment_restarts_in(&mut self);

    /// Performs the actions associated with a restart.
    /// This usually involves resetting the `restarts_in` counter to a new interval
    /// and potentially updating internal state to calculate the next interval.
    /// It also increments the total count of restarts performed.
    fn restart(&mut self);

    /// Returns the total number of restarts performed by this strategy so far.
    fn num_restarts(&self) -> usize;

    /// Checks if a restart should occur based on the current state.
    ///
    /// If `restarts_in()` is 0, this method calls `restart()` and returns `true`.
    /// Otherwise, it calls `increment_restarts_in()` (which typically decrements the counter)
    /// and returns `false`.
    ///
    /// # Returns
    /// `true` if a restart was triggered, `false` otherwise.
    fn should_restart(&mut self) -> bool {
        if self.restarts_in() == 0 {
            self.restart();
            true
        } else {
            self.increment_restarts_in();
            false
        }
    }
}

/// A restart strategy based on the Luby sequence.
///
/// The Luby sequence (u_i) is defined as:
/// u_i = 2^(k-1) if i = 2^k - 1
/// u_i = u_(i - 2^(k-1) + 1) if 2^(k-1) <= i < 2^k - 1
///
/// This sequence has the property of being optimal for repeating an experiment with unknown
/// probability distribution of success time. In SAT solvers, it means restarting after
/// `u_1*N, u_2*N, u_3*N, ...` conflicts (or decision units).
/// The sequence starts 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
///
/// The generic constant `N` is a unit scaling factor for the intervals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Luby<const N: usize> {
    /// Total number of restarts performed.
    restarts: usize,
    /// Number of conflicts/units remaining until the next restart.
    restarts_in: usize,
    /// The current interval (number of conflicts/units) for the next restart,
    /// calculated as `luby(restarts_next) * N`.
    restarts_interval: usize,
    /// The index into the Luby sequence for calculating the next interval.
    restarts_next: usize,
}

impl<const N: usize> Luby<N> {
    /// Calculates the k-th element of the Luby sequence.
    ///
    /// # Parameters
    /// * `x`: The index (1-based) for the Luby sequence.
    ///
    /// # Returns
    /// The Luby number for the given index.
    fn luby(x: usize) -> usize {
        let mut k = 1_usize;
        while (1 << (k - 1)) <= x {
            k = k.wrapping_add(1);
        }
        if x == (1 << (k - 2)) {
            1 << (k - 2)
        } else {
            Self::luby(x - (1 << (k - 2)))
        }
    }
}

impl<const N: usize> Restarter for Luby<N> {
    /// Creates a new `Luby` restarter.
    /// The first restart interval will be `N * luby(1)`.
    /// `restarts_in` is initialized to 0, meaning it will restart on the first call to `should_restart()`.
    fn new() -> Self {
        Self {
            restarts: 0,
            restarts_in: 0,
            restarts_interval: 1,
            restarts_next: 1,
        }
    }

    fn restarts_in(&self) -> usize {
        self.restarts_in
    }

    fn increment_restarts_in(&mut self) {
        self.restarts_in = self.restarts_in.wrapping_sub(1);
    }

    /// Performs a restart:
    /// 1. Increments the restart count.
    /// 2. Sets `restarts_in` to the previously calculated `restarts_interval`.
    /// 3. Calculates the next `restarts_interval` as `Self::luby(self.restarts_next) * N`.
    /// 4. Increments `restarts_next` for the subsequent Luby sequence calculation.
    fn restart(&mut self) {
        self.restarts = self.restarts.wrapping_add(1);
        self.restarts_in = self.restarts_interval;
        self.restarts_interval = Self::luby(self.restarts_next) * N;
        self.restarts_next = self.restarts_next.wrapping_add(1);
    }

    fn num_restarts(&self) -> usize {
        self.restarts
    }
}

/// A geometric restart strategy.
///
/// The interval between restarts is multiplied by a constant factor `N` (where `N` > 1 for
/// increasing intervals) after each restart.
/// The sequence of intervals is `initial, initial*N, initial*N*N, ...`.
/// Here, `initial` seems to be 1 based on `restarts_interval: 1` and then it's multiplied by `N`.
/// The first interval will be 1 (due to `restarts_in: 0` and `restarts_interval: 1` upon first `restart`),
/// then `N`, then `N*N`, etc.
/// The generic constant `N` is the geometric factor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Geometric<const N: usize> {
    /// Total number of restarts performed.
    restarts: usize,
    /// Number of conflicts/units remaining until the next restart.
    restarts_in: usize,
    /// The current interval length for the next restart.
    restarts_interval: usize,
}

impl<const N: usize> Restarter for Geometric<N> {
    /// Creates a new `Geometric` restarter.
    /// `restarts_in` is initialized to 0, meaning it will restart on the first call to `should_restart()`.
    /// The first interval after the initial restart will be 1, the next will be `1*N`, then `1*N*N`, etc.
    fn new() -> Self {
        Self {
            restarts: 0,
            restarts_in: 0,
            restarts_interval: 1,
        }
    }

    fn restarts_in(&self) -> usize {
        self.restarts_in
    }

    fn increment_restarts_in(&mut self) {
        self.restarts_in = self.restarts_in.wrapping_sub(1);
    }

    /// Performs a restart:
    /// 1. Increments the restart count.
    /// 2. Sets `restarts_in` to the current `restarts_interval`.
    /// 3. Updates `restarts_interval` by multiplying it by `N` for the next cycle.
    fn restart(&mut self) {
        self.restarts = self.restarts.wrapping_add(1);
        self.restarts_in = self.restarts_interval;
        self.restarts_interval = self.restarts_interval.wrapping_mul(N);
    }

    fn num_restarts(&self) -> usize {
        self.restarts
    }

    /// Overrides the default `should_restart` from the trait.
    /// This implementation is identical to the default one but is explicitly written out.
    /// If `restarts_in` is 0, it calls `restart()` and returns `true`.
    /// Otherwise, it decrements `restarts_in` and returns `false`.
    fn should_restart(&mut self) -> bool {
        if self.restarts_in == 0 {
            self.restart();
            true
        } else {
            self.restarts_in = self.restarts_in.wrapping_sub(1);
            false
        }
    }
}

/// A fixed interval restart strategy.
///
/// Restarts occur every `N` conflicts (or other units).
/// The generic constant `N` defines this fixed interval.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fixed<const N: usize> {
    /// Total number of restarts performed.
    restarts: usize,
    /// Number of conflicts/units remaining until the next restart.
    restarts_in: usize,
    /// The fixed interval `N` between restarts.
    restarts_interval: usize,
}

impl<const N: usize> Restarter for Fixed<N> {
    /// Creates a new `Fixed` restarter.
    /// `restarts_in` is initialized to 0, meaning it will restart on the first call to `should_restart()`.
    /// The interval for all subsequent restarts will be `N`.
    fn new() -> Self {
        assert!(N > 0, "Fixed interval N must be positive.");
        Self {
            restarts: 0,
            restarts_in: 0,
            restarts_interval: N,
        }
    }

    fn restarts_in(&self) -> usize {
        self.restarts_in
    }

    fn increment_restarts_in(&mut self) {
        self.restarts_in = self.restarts_in.wrapping_sub(1);
    }

    /// Performs a restart:
    /// 1. Increments the restart count.
    /// 2. Resets `restarts_in` to `restarts_interval` (which is fixed at `N`).
    fn restart(&mut self) {
        self.restarts = self.restarts.wrapping_add(1);
        self.restarts_in = self.restarts_interval;
    }

    fn num_restarts(&self) -> usize {
        self.restarts
    }
}

/// A strategy that never triggers a restart.
///
/// This can be used to disable restarts or as a baseline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Never {}

impl Restarter for Never {
    fn new() -> Self {
        Self {}
    }

    /// Returns 0, but `should_restart` will always be false, so this value is not
    /// practically used to countdown to a restart.
    fn restarts_in(&self) -> usize {
        usize::MAX
    }

    /// Does nothing, as no restarts are pending.
    fn increment_restarts_in(&mut self) {}

    /// Does nothing, as restarts are disabled.
    fn restart(&mut self) {}

    /// Always returns 0, as no restarts are ever performed.
    fn num_restarts(&self) -> usize {
        0
    }

    /// Always returns `false`, indicating that a restart should never occur.
    fn should_restart(&mut self) -> bool {
        false
    }
}

/// A linear restart strategy.
///
/// The interval between restarts increases by a fixed amount `N` after each restart.
/// The sequence of intervals is `initial_N, initial_N + N, initial_N + 2N, ...`.
/// The generic constant `N` is the fixed amount by which the interval increases.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Linear<const N: usize> {
    /// Total number of restarts performed.
    restarts: usize,
    /// Number of conflicts/units remaining until the next restart.
    restarts_in: usize,
    /// The current interval length, which increases by `N` after each restart.
    restarts_interval: usize,
}

impl<const N: usize> Restarter for Linear<N> {
    /// Creates a new `Linear` restarter.
    /// `restarts_in` is initialized to 0, meaning it will restart on the first call to `should_restart()`.
    /// The first interval after the initial restart will be `N`, the next `2N`, then `3N`, and so on.
    fn new() -> Self {
        assert!(N > 0, "Linear increment N must be positive.");
        Self {
            restarts: 0,
            restarts_in: 0,
            restarts_interval: N,
        }
    }

    fn restarts_in(&self) -> usize {
        self.restarts_in
    }

    fn increment_restarts_in(&mut self) {
        self.restarts_in -= 1;
    }

    /// Performs a restart:
    /// 1. Increments the restart count.
    /// 2. Sets `restarts_in` to the current `restarts_interval`.
    /// 3. Increases `restarts_interval` by `N` for the next cycle.
    fn restart(&mut self) {
        self.restarts = self.restarts.wrapping_add(1);
        self.restarts_in = self.restarts_interval;
        self.restarts_interval = self.restarts_interval.wrapping_add(N);
    }

    fn num_restarts(&self) -> usize {
        self.restarts
    }
}

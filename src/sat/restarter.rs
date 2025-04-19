use std::fmt::Debug;

pub trait Restarter: Debug + Clone {
    fn new() -> Self;

    fn restarts_in(&self) -> usize;
    fn increment_restarts_in(&mut self);
    fn restart(&mut self);

    fn num_restarts(&self) -> usize;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Luby<const N: usize> {
    restarts: usize,
    restarts_in: usize,
    restarts_interval: usize,
    restarts_next: usize,
}

impl<const N: usize> Luby<N> {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Geometric<const N: usize> {
    restarts: usize,
    restarts_in: usize,
    restarts_interval: usize,
    restarts_next: usize,
}

impl<const N: usize> Restarter for Geometric<N> {
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

    fn restart(&mut self) {
        self.restarts = self.restarts.wrapping_add(1);
        self.restarts_in = self.restarts_interval;
        self.restarts_interval = self.restarts_interval.wrapping_mul(N);
    }

    fn num_restarts(&self) -> usize {
        self.restarts
    }

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fixed<const N: usize> {
    restarts: usize,
    restarts_in: usize,
    restarts_interval: usize,
}

impl<const N: usize> Restarter for Fixed<N> {
    fn new() -> Self {
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

    fn restart(&mut self) {
        self.restarts = self.restarts.wrapping_add(1);
        self.restarts_in = self.restarts_interval;
    }

    fn num_restarts(&self) -> usize {
        self.restarts
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Never {}

impl Restarter for Never {
    fn new() -> Self {
        Self {}
    }

    fn restarts_in(&self) -> usize {
        0
    }

    fn increment_restarts_in(&mut self) {}

    fn restart(&mut self) {}

    fn num_restarts(&self) -> usize {
        0
    }

    fn should_restart(&mut self) -> bool {
        false
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Linear<const N: usize> {
    restarts: usize,
    restarts_in: usize,
    restarts_interval: usize,
}

impl<const N: usize> Restarter for Linear<N> {
    fn new() -> Self {
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

    fn restart(&mut self) {
        self.restarts = self.restarts.wrapping_add(1);
        self.restarts_in = self.restarts_interval;
        self.restarts_interval = self.restarts_interval.wrapping_add(N);
    }

    fn num_restarts(&self) -> usize {
        self.restarts
    }
}

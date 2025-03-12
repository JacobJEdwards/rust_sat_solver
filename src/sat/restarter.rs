pub trait Restarter {
    fn new() -> Self;

    fn restarts_in(&self) -> usize;
    fn increment_restarts_in(&mut self);
    fn restart(&mut self);

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
pub struct Luby {
    restarts: usize,
    restarts_in: usize,
    restarts_interval: usize,
    restarts_next: usize,
}

impl Luby {
    fn luby(x: usize) -> usize {
        let mut k = 1;
        while (1 << (k - 1)) <= x {
            k += 1;
        }
        if x == (1 << (k - 2)) {
            1 << (k - 2)
        } else {
            Self::luby(x - (1 << (k - 2)))
        }
    }
}

impl Restarter for Luby {
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
        self.restarts_in -= 1;
    }

    fn restart(&mut self) {
        self.restarts += 1;
        self.restarts_in = self.restarts_interval;
        self.restarts_interval = Self::luby(self.restarts_next);
        self.restarts_next += 1;
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Geometric {
    restarts: usize,
    restarts_in: usize,
    restarts_interval: usize,
    restarts_next: usize,
}

impl Geometric {}

impl Restarter for Geometric {
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
        self.restarts_in -= 1;
    }

    fn restart(&mut self) {
        self.restarts += 1;
        self.restarts_in = self.restarts_interval;
        self.restarts_interval *= 2;
    }

    fn should_restart(&mut self) -> bool {
        if self.restarts_in == 0 {
            self.restart();
            true
        } else {
            self.restarts_in -= 1;
            false
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fixed {
    restarts: usize,
    restarts_in: usize,
    restarts_interval: usize,
}

impl Fixed {}

impl Restarter for Fixed {
    fn new() -> Self {
        Self {
            restarts: 0,
            restarts_in: 0,
            restarts_interval: 100,
        }
    }

    fn restarts_in(&self) -> usize {
        self.restarts_in
    }

    fn increment_restarts_in(&mut self) {
        self.restarts_in -= 1;
    }

    fn restart(&mut self) {
        self.restarts += 1;
        self.restarts_in = self.restarts_interval;
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

    fn should_restart(&mut self) -> bool {
        false
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Linear {
    restarts: usize,
    restarts_in: usize,
    restarts_interval: usize,
}

impl Linear {}

impl Restarter for Linear {
    fn new() -> Self {
        Self {
            restarts: 0,
            restarts_in: 0,
            restarts_interval: 100,
        }
    }

    fn restarts_in(&self) -> usize {
        self.restarts_in
    }

    fn increment_restarts_in(&mut self) {
        self.restarts_in -= 1;
    }

    fn restart(&mut self) {
        self.restarts += 1;
        self.restarts_in = self.restarts_interval;
        self.restarts_interval += 100;
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Exponential {
    restarts: usize,
    restarts_in: usize,
    restarts_interval: usize,
}

impl Exponential {}

impl Restarter for Exponential {
    fn new() -> Self {
        Self {
            restarts: 0,
            restarts_in: 0,
            restarts_interval: 100,
        }
    }

    fn restarts_in(&self) -> usize {
        self.restarts_in
    }

    fn increment_restarts_in(&mut self) {
        self.restarts_in -= 1;
    }

    fn restart(&mut self) {
        self.restarts += 1;
        self.restarts_in = self.restarts_interval;
        self.restarts_interval *= 2;
    }
}

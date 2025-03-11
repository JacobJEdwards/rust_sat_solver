pub trait Restarter {
    fn new() -> Self;
    
    fn should_restart(&mut self) -> bool;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Luby {
    restarts: usize,
    restarts_in: usize,
    restarts_interval: usize,
    restarts_next: usize,
}

impl Luby {
    fn restart(&mut self) {
        self.restarts += 1;
        self.restarts_in = self.restarts_interval;
        self.restarts_interval = Self::luby(self.restarts_next);
        self.restarts_next += 1;
    }
    
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
pub struct Geometric {
    restarts: usize,
    restarts_in: usize,
    restarts_interval: usize,
    restarts_next: usize,
}

impl Geometric {
    fn restart(&mut self) {
        self.restarts += 1;
        self.restarts_in = self.restarts_interval;
        self.restarts_interval *= 2;
    }
}

impl Restarter for Geometric {
    fn new() -> Self {
        Self {
            restarts: 0,
            restarts_in: 0,
            restarts_interval: 1,
            restarts_next: 1,
        }
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

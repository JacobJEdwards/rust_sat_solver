use core::cmp::PartialEq;
use core::ops::Not;
use std::collections::HashSet;
use core::fmt::Debug;

/// mod clause
type Lit = i32;

const fn variable(lit: Lit) -> i32 {
    lit >> 1
}

const fn negative(v: i32) -> Lit {
    v * 2 + 1
}

fn positive(v: i32) -> Lit {
    v * 2
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Clause {
    pub literals: Vec<Lit>,
    pub deleted: bool,
    pub lbd: usize,
}

impl Clause {
    pub const fn new(literals: Vec<Lit>) -> Self {
        Clause {
            literals,
            deleted: false,
            lbd: 0,
        }
    }

    fn renumber(&self) -> Clause {
        let lits = self.literals.iter().map(|&l| {
            if l < 0 {
                negative(-l - 1)
            } else {
                positive(l - 1)
            }
        }).collect();

        Clause::new(lits)
    }
}

/// mod var value
#[derive(Debug, PartialEq, Clone, Eq, Copy)]
pub enum VarValue {
    TRUE, FALSE, UNDEFINED
}

impl Not for VarValue {
    type Output = VarValue;

    fn not(self) -> VarValue {
        match self {
            VarValue::TRUE => VarValue::FALSE,
            VarValue::FALSE => VarValue::TRUE,
            VarValue::UNDEFINED => VarValue::UNDEFINED
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
struct VarState {
    pub value: VarValue,
    pub reason: Option<Clause>,
    pub level: i32
}

/// mod restarter
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Restarter {
    luby_multiplier_constant: usize,
    restart_number: usize,
    num_conflict_after_restart: usize,
    luby_position: usize,
}

impl Restarter {
    pub const fn new() -> Self {
        Restarter {
            luby_multiplier_constant: 50,
            restart_number: 50,
            num_conflict_after_restart: 0,
            luby_position: 1,
        }
    }

    pub fn luby(i: i32, initial_deg: i32) -> i32 {
        if i == 2 {
            return 1;
        }
        let mut deg = initial_deg;
        while deg <= i {
            deg *= 2;
        }
        while deg / 2 > i {
            deg /= 2;
        }
        if deg - 1 == i {
            return deg / 2;
        }
        Self::luby(i - deg / 2 + 1, deg / 2)
    }

    pub fn restart(&mut self) {
        self.restart_number = self.luby_multiplier_constant * Self::luby(self.luby_position as i32, 1) as usize;
        self.luby_position += 1;
    }

    pub fn update(&mut self) -> bool {
        self.num_conflict_after_restart += 1;
        if self.num_conflict_after_restart >= self.restart_number {
            self.num_conflict_after_restart = 0;
            self.restart();
            true
        } else {
        false}
    }
}

/// mod var selector
trait VariableSelector: Clone + PartialEq + Debug {
    fn new() -> Self where Self: Sized;

    fn init_assumptions(&mut self, assumptions: Vec<Lit>);
    fn build(&mut self, clauses: Vec<Clause>);
    fn next_decision(&mut self, vars: &[VarState], level: i32) -> i32;
    fn add_variable(&mut self);
    fn update(&mut self, lemma: &Clause);
    fn backtrack(&mut self, variable: i32);
}

#[derive(Debug, PartialEq, Clone)]
struct VSIDS {
    number_of_variables: usize,
    decay: usize,
    multiplier: f64,
    activity_limit: f64,
    activity_inc: f64,
    number_of_conflicts: usize,
    activity: Vec<f64>,
    assumptions: Vec<Lit>,
}

impl VSIDS {
    fn max_var(&self, vars: &[VarState]) -> Lit {
        let mut max = -1.0;
        let mut max_var = 0;
        for (i, var) in vars.iter().enumerate() {
            if var.value == VarValue::UNDEFINED && self.activity[i] > max {
                max = self.activity[i];
                max_var = i;
            }
        }
        max_var as Lit
    }
}

impl VariableSelector for VSIDS {
    fn new() -> Self {
        VSIDS {
            number_of_variables: 0,
            decay: 50,
            multiplier: 2.0,
            number_of_conflicts: 0,
            activity_inc: 1.0,
            activity_limit: 1e100,
            activity: Vec::new(),
            assumptions: Vec::new(),
        }
    }
    fn init_assumptions(&mut self, assumptions: Vec<Lit>) {
        self.assumptions = assumptions;
    }

    fn build(&mut self, clauses: Vec<Clause>) {
        while self.activity.len() < self.number_of_variables {
            self.activity.push(0.0);
        }

        for c in clauses {
            for &lit in &c.literals {
                let var = variable(lit);
                self.activity[var as usize] += self.activity_inc;
            }
        }
        // TODO: binary heap
    }

    fn next_decision(&mut self, vars: &[VarState], _: i32) -> i32 {
        if self.assumptions.iter().any(|&lit| vars[variable(lit) as usize].value == VarValue::FALSE) {
            return -1;
        }

        let max = self.max_var(vars);
        *self.assumptions.iter().find(|&&lit| vars[variable(lit) as usize].value ==
            VarValue::UNDEFINED).unwrap_or(&max)
    }

    fn add_variable(&mut self) {
        self.activity.push(0.0);
        self.number_of_variables += 1;
    }

    fn update(&mut self, lemma: &Clause) {
        for &lit in &lemma.literals {
            let var = variable(lit);
            self.activity[var as usize] += self.activity_inc;
        }

        self.number_of_conflicts += 1;
        if self.number_of_conflicts == self.decay {
            self.activity_inc *= self.multiplier;
            self.number_of_conflicts = 0;
            if self.activity_inc > self.activity_limit {
                for i in 0..self.activity.len() {
                    self.activity[i] /= self.activity_inc;
                }
                self.activity_inc = 1.0;
            }
        }
    }

    fn backtrack(&mut self, variable: i32) {

    }
}

/// mod cdcl
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Solvertype {
    Incremental,
    NonIncremental,
}

#[derive(Debug, PartialEq, Clone)]
pub struct CDCL {
    pub solver_type: Solvertype,
    pub constraints : Vec<Clause>,
    pub learned: Vec<Clause>,
    pub number_of_variables: usize,
    vars: Vec<VarState>,
    pub trail: Vec<Lit>,
    pub qhead: usize,
    pub watchers: Vec<Vec<Clause>>,
    pub reduce_number: usize,
    pub reduce_increment: usize,
    pub level: usize,
    pub minimise_marks: Vec<usize>,
    pub mark: usize,
    restart: Restarter,
    selector: VSIDS,
    pub polarity: Vec<VarValue>,
    pub seen: Vec<bool>,
    pub assumptions: Vec<i32>,
}

impl CDCL {
    pub fn new(initial: Vec<Clause>, initial_vars_num: usize) -> Self {
        let mut solver = CDCL {
            solver_type: Solvertype::Incremental,
            constraints: Vec::new(),
            learned: Vec::new(),
            number_of_variables: 0,
            vars: Vec::new(),
            trail: Vec::new(),
            qhead: 0,
            watchers: Vec::new(),
            reduce_number: 6000,
            reduce_increment: 500,
            level: 0,
            minimise_marks: Vec::new(),
            mark: 0,
            restart: Restarter::new(),
            selector: VSIDS::new(),
            polarity: Vec::new(),
            seen: Vec::new(),
            assumptions: Vec::new(),
        };
        solver.reserve_vars(initial_vars_num);
        let initial_clauses: Vec<Clause> = initial.iter().map(Clause::renumber).collect();
        for clause in initial_clauses {
            solver.new_clause(&mut clause.clone());
        }
        solver.polarity = vec![VarValue::UNDEFINED; solver.number_of_variables + 1];
        solver
    }

    fn unchecked_enqueue(&mut self, lit: Lit, reason: Option<Clause>) {
        self.set_value(lit, VarValue::TRUE);
        let v = variable(lit);
        self.vars[v as usize].reason = reason;
        self.vars[v as usize].level = self.level as i32;
        self.trail.push(lit);
    }

    fn get_value(&self, lit: Lit) -> VarValue {
        let v = variable(lit);
        if self.vars[v as usize].value == VarValue::UNDEFINED {
            return VarValue::UNDEFINED;
        }

        if lit % 2 == 1 {
            !self.vars[v as usize].value
        } else {
            self.vars[v as usize].value
        }
    }

    fn set_value(&mut self, lit: Lit, value: VarValue) {
        let v = variable(lit);
        if lit % 2 == 1 {
            self.vars[v as usize].value = !value;
        } else {
            self.vars[v as usize].value = value;
        }
    }

    fn reserve_vars(&mut self, max: usize) {
        if self.number_of_variables < max {
            self.add_variable();
        }
    }

    fn add_variable(&mut self) -> usize {
        self.number_of_variables += 1;
        self.selector.add_variable();
        self.vars.push(VarState {
            value: VarValue::UNDEFINED,
            reason: None,
            level: 0,
        });
        self.polarity.push(VarValue::UNDEFINED);

        self.watchers.push(Vec::new());
        self.watchers.push(Vec::new());

        self.minimise_marks.push(0);
        self.minimise_marks.push(0);

        self.seen.push(false);

        self.number_of_variables
    }

    pub fn new_clause(&mut self, clause: &mut Clause) {
        assert_eq!(self.level, 0);

        let max_var = clause.literals.iter().map(|&lit| variable(lit)).max().unwrap_or(0);

        while self.number_of_variables <= max_var as usize {
            self.add_variable();
        }

        if clause.literals.iter().any(|&lit| self.get_value(lit) == VarValue::TRUE) {
            return;
        }

        clause.literals.retain(|lit| self.get_value(*lit) != VarValue::FALSE);
        // if (clause.any { (it xor 1) in clause }) {
        //     return
        // }

        if clause.literals.len() == 1 {
            self.unchecked_enqueue(clause.literals[0], None);
        } else {
            self.add_constraint(clause);
        }
    }

    fn trail_remove_last(&mut self) {
        let lit = self.trail.pop().unwrap();
        let v = variable(lit);
        self.polarity[v as usize] = self.get_value(positive(v));
        self.set_value(positive(v), VarValue::UNDEFINED);
        self.vars[v as usize].reason = None;
        self.vars[v as usize].level = -1;
        self.selector.backtrack(v);
    }

    fn clear_trail(&mut self, until: i32) {
        while !self.trail.is_empty() && self.vars[variable(*self.trail.last().unwrap()) as usize].level > until {
            self.trail_remove_last();
        }
    }

    fn reduce_db(&mut self) {
        self.learned.sort_by(|a, b| a.lbd.cmp(&b.lbd));
        let deletion_limit = self.learned.len() / 2;
        for i in 0..self.learned.len() {
            if i >= deletion_limit {
                break;
            }
            if !self.learned[i].deleted {
                self.learned[i].deleted = true;
            }
        }
        self.learned.retain(|c| !c.deleted);
    }

    pub fn solve(&mut self) -> Option<Vec<i32>> {
        let mut num_conflicts = 0;
        let mut num_decisions = 0;

        if self.constraints.is_empty() {
            return Some(self.get_model());
        }
        if self.constraints.iter().any(|c| c.literals.is_empty()) {
            return None;
        }

        self.selector.build(self.constraints.clone());

        loop {
            let conflict = self.propagate();

            match conflict {
                Some(conflict) => {
                    num_conflicts += 1;

                    if self.level == 0 {
                        return None;
                    }

                    let mut lemma = self.analyse_conflict(conflict);
                    lemma.lbd = lemma.literals.iter().map(|&lit| variable(lit)).collect::<HashSet<_>>().len();
                    self.backtrack(&lemma);
                    self.qhead = self.trail.len();

                    if lemma.literals.len() == 1 {
                        self.unchecked_enqueue(lemma.literals[0], None);
                    } else {
                        self.unchecked_enqueue(lemma.literals[0], Some(lemma.clone()));
                        self.add_learned(&lemma);
                    }

                    if self.learned.len() > self.reduce_number {
                        self.reduce_number += self.reduce_increment;
                        // self.restart.restart();
                        self.reduce_db();
                    }
                    self.selector.update(&lemma);
                    self.restart.update();
                }
                None => {
                    assert_eq!(self.qhead, self.trail.len());

                    if self.trail.len() >= self.number_of_variables {
                        let model = Some(self.get_model());
                        self.reset();
                        return model;
                    }

                    self.level += 1;
                    let mut next_decision = self.selector.next_decision(&self.vars, self.level as i32);
                    num_decisions += 1;

                    if next_decision == -1 {
                        self.reset();
                        return None;
                    }

                    if self.level > self.assumptions.len() && self.polarity[variable(next_decision) as usize] == VarValue::FALSE {
                        next_decision = negative(variable(next_decision));
                    }

                    self.unchecked_enqueue(next_decision, None);
                }
            }
        }
    }

    fn reset(&mut self) {
        self.level = 0;
        self.clear_trail(0);
        self.qhead = self.trail.len();
    }

    fn get_model(&self) -> Vec<i32> {
        self.vars.iter().enumerate().map(|(i, v)| {
            match v.value {
                VarValue::TRUE => (i + 1) as i32,
                VarValue::UNDEFINED => (i + 1) as i32,
                VarValue::FALSE => -(i as i32) - 1,
            }
        }).collect()
    }

    fn add_watchers(&mut self, clause: &Clause) {
        assert!(clause.literals.len() > 1);
        self.watchers[clause.literals[0] as usize].push(clause.clone());
        self.watchers[clause.literals[1] as usize].push(clause.clone());
    }

    fn add_constraint(&mut self, clause: &Clause) {
        assert_ne!(clause.literals.len(), 1);
        self.constraints.push(clause.clone());
        if !clause.literals.is_empty() {
            self.add_watchers(clause);
        }
    }

    fn add_learned(&mut self, clause: &Clause) {
        assert_ne!(clause.literals.len(), 1);
        self.learned.push(clause.clone());
        if !clause.literals.is_empty() {
            self.add_watchers(clause);
        }
    }

    fn propagate(&mut self) -> Option<Clause> {
        let mut conflict: Option<Clause> = None;
        while self.qhead < self.trail.len() {
            let lit = self.trail[self.qhead];
            self.qhead += 1;
            if self.get_value(lit) == VarValue::FALSE {
                let v = variable(lit);
                let reason = self.vars[v as usize].reason.clone();
                return reason;
            }

            let mut to_keep: Vec<Clause> = Vec::new();
            for mut clause in self.watchers[(lit ^ 1) as usize].clone() {
                if clause.deleted {
                    continue;
                }
                to_keep.push(clause.clone());
                if conflict.is_some() {
                    continue;
                }
                if variable(clause.literals[0]) == variable(lit) {
                    clause.literals.swap(0, 1);
                }
                if self.get_value(clause.literals[0]) == VarValue::TRUE {
                    continue;
                }
                let mut first_not_false = -1;
                for ind in 2..clause.literals.len() {
                    if self.get_value(clause.literals[ind]) != VarValue::FALSE {
                        first_not_false = ind as i32;
                        break;
                    }
                }
                if first_not_false == -1 && self.get_value(clause.literals[0]) == VarValue::FALSE {
                    conflict = Some(clause.clone());
                } else if first_not_false == -1 {
                    self.unchecked_enqueue(clause.literals[0], Some(clause.clone()));
                } else {
                    self.watchers[clause.literals[first_not_false as usize] as usize].push(clause.clone());
                    clause.literals.swap(first_not_false as usize, 1);
                    to_keep.remove(to_keep.len() - 1);
                }
            }
            self.watchers[(lit ^ 1) as usize] = to_keep;
            if conflict.is_some() {
                break
            }
        }
        conflict
    }

    fn backtrack(&mut self, clause: &Clause) {
        self.level = if clause.literals.len() > 1 {
            let v = variable(clause.literals[1]);
            self.vars[v as usize].level as usize
        } else {
            0
        };
        self.clear_trail(self.level as i32);
    }

    fn minimise(&mut self, clause: &Clause) -> Clause {
        self.mark += 1;
        clause.literals.iter().for_each(|&l| self.minimise_marks[l as usize] = self.mark);

        let literals = clause.literals.iter().filter(|&l| {
            let v = variable(*l);
            let reason = self.vars[v as usize].reason.clone();
            if reason.is_none() {
                return false;
            }
            let reason = reason.unwrap();
            reason.literals.iter().all(|&l| self.minimise_marks[l as usize] == self.mark)
        }).copied().collect();

        Clause::new(literals)
    }

    fn analyse_conflict(&mut self, conflict: Clause) -> Clause {
        let mut num_active = 0;
        let mut lemma = HashSet::new();

        conflict.literals.iter().for_each(|&lit| {
            let v = variable(lit);
            if self.vars[v as usize].level == self.level as i32 {
                self.seen[v as usize] = true;
                num_active += 1;
            } else {
                lemma.insert(lit);
            }
        });
        let mut ind = self.trail.len() - 1;

        while num_active > 1 {
            let v = variable(self.trail[ind]);
            ind -= 1;

            let reason = self.vars[v as usize].reason.clone();
            if let Some(reason) = reason {
                reason.literals.iter().for_each(|&lit| {
                    let current = variable(lit);
                    if self.vars[current as usize].level != self.level as i32 {
                        lemma.insert(lit);
                    } else if current != v && !self.seen[current as usize] {
                        self.seen[current as usize] = true;
                        num_active += 1;
                    }
                });
            }
            self.seen[v as usize] = false;
            num_active -= 1;
        }

        let mut fin: Option<Clause> = None;
        let last_seen = self.trail.iter().rfind(|&&lit| {
            let v = variable(lit);
            self.seen[v as usize]
        });
        if let Some(last_seen) = last_seen {
            let v = variable(*last_seen);
            let to_insert = if self.get_value(positive(v)) == VarValue::TRUE {
                negative(v)
            } else {
                positive(v)
            };
            lemma.insert(to_insert);
            let mut new_clause = self.minimise(&Clause::new(lemma.iter().cloned().collect()));
            let uip_index = new_clause.literals.iter().position(|&lit| variable(lit) == v).unwrap();
            new_clause.literals.swap(0, uip_index);
            self.seen[v as usize] = false;
            fin = Some(new_clause);
        }

        let mut fin = fin.unwrap();
        if fin.literals.len() > 1 {
            // val secondMax = newClause.drop(1).indices.maxByOrNull { vars[variable(newClause[it + 1])].level } ?: 0
            // newClause.swap(1, secondMax + 1)
            let second_max = fin.literals.iter().skip(1).enumerate().max_by_key(|&(_, &lit)| self
                .vars[variable(lit) as usize].level).unwrap().0;
            fin.literals.swap(1, second_max + 1);
        }
        fin
    }
}
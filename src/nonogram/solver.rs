use crate::sat::cnf::Cnf;
use std::cmp::max;
use std::fmt::Display;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Cell {
    Empty = 2,
    Filled = 1,
    Unknown = 0,
}

impl Display for Cell {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Cell::Empty => write!(f, "."),
            Cell::Filled => write!(f, "#"),
            Cell::Unknown => write!(f, " "),
        }
    }
}

type Constraint = Vec<i32>;
type Size = usize;
type Mask = Vec<i32>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Nonogram {
    rows: Vec<Constraint>,
    cols: Vec<Constraint>,
    solution: Vec<Vec<Cell>>,
}

impl Nonogram {
    pub fn new(rows: Vec<Constraint>, cols: Vec<Constraint>) -> Self {
        let row_size = rows.len();
        let col_size = cols.len();
        let solution = vec![vec![Cell::Unknown; col_size]; row_size];
        Nonogram {
            rows,
            cols,
            solution,
        }
    }

    pub fn decode(&self, assignment: Vec<i32>) -> Vec<Vec<Cell>> {
        let mut solution = self.solution.clone();
        for (i, _) in self.rows.iter().enumerate() {
            for (j, _) in self.cols.iter().enumerate() {
                let fill = Variable::new(i + 1, j + 1, Cell::Filled).encode(self.clone());
                let empty = Variable::new(i + 1, j + 1, Cell::Empty).encode(self.clone());

                if assignment.contains(&(fill as i32)) {
                    solution[i][j] = Cell::Filled;
                } else if assignment.contains(&(empty as i32)) {
                    solution[i][j] = Cell::Empty;
                }
            }
        }
        solution
    }

    pub fn to_cnf(&self) -> Cnf {
        let cell_clauses = generate_cell_clauses(self.clone());
        let cell_unique_clauses = generate_cell_unique_clauses(self.clone());

        let row_clauses = generate_row_clauses(self.clone());
        let col_clauses = generate_col_clauses(self.clone());

        let clauses = cell_clauses
            .iter()
            .chain(cell_unique_clauses.iter())
            .chain(row_clauses.iter())
            .chain(col_clauses.iter())
            .cloned()
            .collect();

        Cnf::new(clauses)
    }
}

fn generate_cell_clauses(nonogram: Nonogram) -> Vec<Vec<i32>> {
    let mut clauses = Vec::new();
    for (i, _) in nonogram.rows.iter().enumerate() {
        for (j, _) in nonogram.cols.iter().enumerate() {
            let fill = Variable::new(i + 1, j + 1, Cell::Filled).encode(nonogram.clone());
            let empty = Variable::new(i + 1, j + 1, Cell::Empty).encode(nonogram.clone());

            let clause = vec![-(fill as i32), -(empty as i32)];
            clauses.push(clause);
        }
    }
    clauses
}

fn generate_cell_unique_clauses(nonogram: Nonogram) -> Vec<Vec<i32>> {
    let mut clauses = Vec::new();
    for (i, _) in nonogram.rows.iter().enumerate() {
        for (j, _) in nonogram.cols.iter().enumerate() {
            let fill = Variable::new(i + 1, j + 1, Cell::Filled).encode(nonogram.clone());
            let empty = Variable::new(i + 1, j + 1, Cell::Empty).encode(nonogram.clone());

            let clause = vec![-(fill as i32), -(empty as i32)];
            clauses.push(clause);
        }
    }
    clauses
}

fn generate_row_clauses(_: Nonogram) -> Vec<Vec<i32>> {
    todo!()
}

fn generate_col_clauses(_: Nonogram) -> Vec<Vec<i32>> {
    todo!()
}

fn encode_cell(nonogram: Nonogram, col_index: usize, row_index: usize, mask: Mask) -> usize {
    let cell = mask[row_index];
    let var = Variable::new(
        row_index + 1,
        col_index + 1,
        if cell >= 1 { Cell::Filled } else { Cell::Empty },
    );
    var.encode(nonogram)
}

fn generate_possible_solutions(
    nonogram: Nonogram,
    size: Size,
    combinations: Constraint,
) -> Vec<Vec<i32>> {
    todo!("Generate all possible solutions for a given row or column")
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Variable {
    row: usize,
    col: usize,
    fill: Cell,
}

impl Variable {
    fn new(row: usize, col: usize, fill: Cell) -> Self {
        Variable { row, col, fill }
    }

    fn encode(&self, nonogram: Nonogram) -> usize {
        let board_max = max(nonogram.rows.len(), nonogram.cols.len());
        (self.row - 1) * board_max * 2 + (self.col - 1) * 2 + self.fill as usize
    }
}

use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::solver::Solutions;
use std::collections::HashMap;
use std::fmt::Display;
use std::num::NonZeroI32;

/// Represents the state of a cell in a Nonogram puzzle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Cell {
    /// Cell is unknown, not yet filled or empty.
    Unknown = 0,
    /// Cell is filled with a block.
    Filled = 1,
    /// Cell is empty, indicating no block is present.
    Empty = 2,
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

type Constraint = Vec<u32>;
type Size = usize;
type Pattern = Vec<Cell>;

/// Represents a Nonogram puzzle, including its constraints and solution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Nonogram {
    rows: Vec<Constraint>,
    cols: Vec<Constraint>,
    solution: Vec<Vec<Cell>>,
}

impl Display for Nonogram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Nonogram:")?;
        writeln!(f, "Rows: {:?}", self.rows)?;
        writeln!(f, "Cols: {:?}", self.cols)?;

        for row in &self.solution {
            for cell in row {
                write!(f, "{}", cell)?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl Nonogram {
    /// Creates a new Nonogram instance with the given row and column constraints.
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

    /// returns the number of rows in the Nonogram.
    pub fn num_rows(&self) -> usize {
        self.rows.len()
    }

    /// returns the number of columns in the Nonogram.
    pub fn num_cols(&self) -> usize {
        self.cols.len()
    }

    /// decodes a given assignment of variables into a solution grid.
    pub fn decode(&self, assignment: &Solutions) -> Vec<Vec<Cell>> {
        let mut solution = vec![vec![Cell::Unknown; self.num_cols()]; self.num_rows()];
        let assignment_set: std::collections::HashSet<NonZeroI32> =
            assignment.iter().cloned().collect();

        for r in 0..self.num_rows() {
            for c in 0..self.num_cols() {
                let fill_var = Variable::new(r, c, Cell::Filled).encode(self);
                let empty_var = Variable::new(r, c, Cell::Empty).encode(self);

                let fill_var = NonZeroI32::new(fill_var as i32).unwrap();
                let empty_var = NonZeroI32::new(empty_var as i32).unwrap();

                if assignment_set.contains(&(fill_var)) {
                    solution[r][c] = Cell::Filled;
                } else if assignment_set.contains(&(empty_var)) {
                    solution[r][c] = Cell::Empty;
                }
            }
        }

        solution
    }

    /// Converts the Nonogram into a CNF (Conjunctive Normal Form) representation suitable for SAT solving.
    pub fn to_cnf<L: Literal, S: LiteralStorage<L>>(&self) -> Cnf<L, S> {
        let num_vars_cell = self.num_rows() * self.num_cols() * 2;
        let mut next_aux_var = (num_vars_cell + 1) as u32;

        println!("Generating cell clauses...");
        let cell_clauses = generate_cell_clauses(self);
        println!("Generating cell unique clauses...");
        let cell_unique_clauses = generate_cell_unique_clauses(self);

        println!("Generating row clauses...");
        let (row_clauses, next_aux_var_after_rows) =
            generate_line_clauses(self, true, next_aux_var);
        next_aux_var = next_aux_var_after_rows;
        println!("Generating column clauses...");
        let (col_clauses, _) = generate_line_clauses(self, false, next_aux_var);

        println!("Combining clauses...");
        let all_clauses: Vec<Vec<i32>> = cell_clauses
            .into_iter()
            .chain(cell_unique_clauses)
            .chain(row_clauses)
            .chain(col_clauses)
            .collect();

        println!(
            "Generated {} clauses with {} variables.",
            all_clauses.len(),
            next_aux_var - 1
        );
        Cnf::new(all_clauses)
    }
}

fn generate_cell_clauses(nonogram: &Nonogram) -> Vec<Vec<i32>> {
    let mut clauses = Vec::new();
    for r in 0..nonogram.num_rows() {
        for c in 0..nonogram.num_cols() {
            let fill_var = Variable::new(r, c, Cell::Filled).encode(nonogram);
            let empty_var = Variable::new(r, c, Cell::Empty).encode(nonogram);

            clauses.push(vec![-(fill_var as i32), -(empty_var as i32)]);
        }
    }
    clauses
}

fn generate_cell_unique_clauses(nonogram: &Nonogram) -> Vec<Vec<i32>> {
    let mut clauses = Vec::new();
    for r in 0..nonogram.num_rows() {
        for c in 0..nonogram.num_cols() {
            let fill_var = Variable::new(r, c, Cell::Filled).encode(nonogram);
            let empty_var = Variable::new(r, c, Cell::Empty).encode(nonogram);

            clauses.push(vec![fill_var as i32, empty_var as i32]);
        }
    }
    clauses
}

fn generate_line_clauses(
    nonogram: &Nonogram,
    is_row: bool,
    mut next_aux_var: u32,
) -> (Vec<Vec<i32>>, u32) {
    let mut clauses = Vec::new();
    let outer_loop_size = if is_row {
        nonogram.num_rows()
    } else {
        nonogram.num_cols()
    };
    let line_size = if is_row {
        nonogram.num_cols()
    } else {
        nonogram.num_rows()
    };
    let constraints_vec = if is_row {
        &nonogram.rows
    } else {
        &nonogram.cols
    };

    let mut memo = HashMap::new();

    for i in 0..outer_loop_size {
        let constraint = &constraints_vec[i];
        println!(
            "  Processing {} {}: Constraint {:?}, Size {}",
            if is_row { "Row" } else { "Col" },
            i,
            constraint,
            line_size
        );

        let possible_patterns = generate_possible_solutions_memo(line_size, constraint, &mut memo);
        println!(
            "    Found {} possible patterns for {} {}",
            possible_patterns.len(),
            if is_row { "Row" } else { "Col" },
            i
        );

        if possible_patterns.is_empty() {
            println!("Warning: No possible patterns found for {} {} with constraints {:?}. Puzzle might be unsatisfiable.", if is_row {"Row"} else {"Col"}, i, constraint);
            clauses.push(vec![]);
            continue;
        }

        let aux_vars: Vec<u32> = (0..possible_patterns.len())
            .map(|_| {
                let var = next_aux_var;
                next_aux_var += 1;
                var
            })
            .collect();

        clauses.push(aux_vars.iter().map(|&v| v as i32).collect());

        for j in 0..aux_vars.len() {
            for k in (j + 1)..aux_vars.len() {
                clauses.push(vec![-(aux_vars[j] as i32), -(aux_vars[k] as i32)]);
            }
        }

        for (pattern_idx, pattern) in possible_patterns.iter().enumerate() {
            let aux_var = aux_vars[pattern_idx];
            for k in 0..line_size {
                let cell_state = pattern[k];
                let (r, c) = if is_row { (i, k) } else { (k, i) };
                let cell_var = Variable::new(r, c, cell_state).encode(nonogram);

                clauses.push(vec![-(aux_var as i32), cell_var as i32]);
            }
        }
    }

    (clauses, next_aux_var)
}

fn generate_possible_solutions_memo(
    size: Size,
    constraint: &Constraint,
    memo: &mut HashMap<(Size, Constraint), Vec<Pattern>>,
) -> Vec<Pattern> {
    let key = (size, constraint.clone());
    if let Some(cached) = memo.get(&key) {
        return cached.clone();
    }

    let mut solutions = Vec::new();
    generate_recursive(
        size,
        constraint,
        0,
        0,
        &mut vec![Cell::Unknown; size],
        &mut solutions,
    );

    memo.insert(key, solutions.clone());
    solutions
}

fn generate_recursive(
    size: Size,
    constraints: &Constraint,
    constraint_idx: usize,
    start_pos: usize,
    current_pattern: &mut Pattern,
    solutions: &mut Vec<Pattern>,
) {
    if constraint_idx == constraints.len() {
        for i in start_pos..size {
            if current_pattern[i] == Cell::Unknown {
                current_pattern[i] = Cell::Empty;
            }
        }
        solutions.push(current_pattern.clone());
        return;
    }

    let block_len = constraints[constraint_idx] as usize;
    let remaining_constraints = &constraints[(constraint_idx + 1)..];
    let min_len_for_remaining =
        remaining_constraints.iter().sum::<u32>() as usize + remaining_constraints.len();

    for pos in start_pos..=size {
        let end_pos = pos + block_len;

        if end_pos > size {
            break;
        }

        let space_needed_after = if constraint_idx < constraints.len() - 1 {
            min_len_for_remaining + 1
        } else {
            0
        };
        if end_pos + space_needed_after > size {
            continue;
        }

        let mut possible = true;
        for i in pos..end_pos {
            if current_pattern[i] == Cell::Empty {
                possible = false;
                break;
            }
        }
        if !possible {
            continue;
        }

        if end_pos < size && current_pattern[end_pos] == Cell::Filled {
            possible = false;
        }
        if !possible {
            continue;
        }

        let original_pattern_slice: Vec<Cell> = current_pattern[pos..].to_vec();

        for i in start_pos..pos {
            if current_pattern[i] == Cell::Unknown {
                current_pattern[i] = Cell::Empty;
            } else if current_pattern[i] == Cell::Filled {
                possible = false;
                break;
            }
        }
        if !possible {
            current_pattern[start_pos..pos].copy_from_slice(&original_pattern_slice[(start_pos - pos)..0]);
            continue;
        }

        for i in pos..end_pos {
            current_pattern[i] = Cell::Filled;
        }

        let next_start_pos;
        if end_pos < size {
            current_pattern[end_pos] = Cell::Empty;
            next_start_pos = end_pos + 1;
        } else {
            next_start_pos = end_pos;
        }

        generate_recursive(
            size,
            constraints,
            constraint_idx + 1,
            next_start_pos,
            current_pattern,
            solutions,
        );

        for i in pos..current_pattern
            .len()
            .min(pos + original_pattern_slice.len())
        {
            current_pattern[i] = original_pattern_slice[i - pos];
        }
        if end_pos < size {
            if end_pos - pos < original_pattern_slice.len() {
                current_pattern[end_pos] = original_pattern_slice[end_pos - pos];
            } else {
                current_pattern[end_pos] = Cell::Unknown;
            }
        }
    }

}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Variable {
    /// 0-based row index
    row: usize,
    /// 0-based column index
    col: usize,
    /// State represented by this variable
    fill: Cell,
}

impl Variable {
    /// Creates a new variable representation.
    /// Uses 0-based indexing internally for row/col.
    fn new(row: usize, col: usize, fill: Cell) -> Self {
        assert!(
            fill == Cell::Filled || fill == Cell::Empty,
            "Variable must represent Filled or Empty state"
        );
        Variable { row, col, fill }
    }

    /// Encodes the variable into a unique positive integer for the SAT solver.
    /// 1-based result.
    fn encode(&self, nonogram: &Nonogram) -> u32 {
        let num_cols = nonogram.num_cols();
        let base = (self.row * num_cols + self.col) * 2;
        (base + self.fill as usize) as u32
    }
}

/// Parses a Nonogram from a string description.
/// Format Assumption:
/// rows <num_rows>
/// cols <num_cols>
/// <row_1_constraint_1> <row_1_constraint_2> ...
/// ... (num_rows lines)
/// <col_1_constraint_1> <col_1_constraint_2> ...
/// ... (num_cols lines)
/// Constraints are space-separated positive integers. Empty lines for constraints mean [0].
pub fn parse_nonogram(input: &str) -> Result<Nonogram, String> {
    let mut lines = input.lines().map(str::trim).filter(|l| !l.is_empty());

    let mut num_rows: Option<usize> = None;
    let mut num_cols: Option<usize> = None;

    if let Some(line) = lines.next() {
        if line.starts_with("rows ") {
            num_rows = line.split_whitespace().nth(1).and_then(|s| s.parse().ok());
        } else {
            return Err("Expected 'rows <num>' format".to_string());
        }
    } else {
        return Err("Missing 'rows' line".to_string());
    }

    if let Some(line) = lines.next() {
        if line.starts_with("cols ") {
            num_cols = line.split_whitespace().nth(1).and_then(|s| s.parse().ok());
        } else {
            return Err("Expected 'cols <num>' format".to_string());
        }
    } else {
        return Err("Missing 'cols' line".to_string());
    }

    let num_rows = num_rows.ok_or("Invalid number for rows")?;
    let num_cols = num_cols.ok_or("Invalid number for cols")?;

    if num_rows == 0 || num_cols == 0 {
        return Err("Rows and columns must be positive".to_string());
    }

    let mut rows = Vec::with_capacity(num_rows);
    for i in 0..num_rows {
        let line = lines
            .next()
            .ok_or(format!("Missing row constraint line {}", i + 1))?;
        let constraint: Constraint = line
            .split_whitespace()
            .map(|s| s.parse::<u32>())
            .collect::<Result<_, _>>()
            .map_err(|e| format!("Invalid number in row constraint {}: {}", i + 1, e))?;
        if constraint.is_empty() || (constraint.len() == 1 && constraint[0] == 0) {
            rows.push(vec![]);
        } else {
            rows.push(constraint);
        }
    }

    let mut cols = Vec::with_capacity(num_cols);
    for i in 0..num_cols {
        let line = lines
            .next()
            .ok_or(format!("Missing column constraint line {}", i + 1))?;
        let constraint: Constraint = line
            .split_whitespace()
            .map(|s| s.parse::<u32>())
            .collect::<Result<_, _>>()
            .map_err(|e| format!("Invalid number in column constraint {}: {}", i + 1, e))?;
        if constraint.is_empty() || (constraint.len() == 1 && constraint[0] == 0) {
            cols.push(vec![]);
        } else {
            cols.push(constraint);
        }
    }

    if lines.next().is_some() {
        return Err("Extra lines found after column constraints".to_string());
    }

    Ok(Nonogram::new(rows, cols))
}

/// Parses a Nonogram from a file.
pub fn parse_nonogram_file(file_path: &str) -> Result<Nonogram, String> {
    let content = std::fs::read_to_string(file_path)
        .map_err(|e| format!("Failed to read file '{}': {}", file_path, e))?;
    parse_nonogram(&content)
}
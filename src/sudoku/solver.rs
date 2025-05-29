use crate::sat::clause_storage::LiteralStorage;
use crate::sat::cnf::Cnf;
use crate::sat::literal::Literal;
use crate::sat::solver::Solutions;
use itertools::Itertools;
use std::fmt::Display;
use std::num::NonZeroI32;
use std::path::PathBuf;

/// Represents a Sudoku board as a 2D vector of numbers.
///
/// `0` typically represents an empty cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Board(Vec<Vec<usize>>);

impl Display for Board {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for row in &self.0 {
            writeln!(
                f,
                "{}",
                row.iter()
                    .map(std::string::ToString::to_string)
                    .collect_vec()
                    .join(" ")
            )?;
        }
        Ok(())
    }
}

impl Board {
    /// Creates a new `Board` from a 2D vector.
    ///
    /// # Arguments
    ///
    /// * `board`: A `Vec<Vec<usize>>` representing the Sudoku grid.
    #[must_use]
    pub const fn new(board: Vec<Vec<usize>>) -> Self {
        Self(board)
    }
}

impl From<Vec<Vec<usize>>> for Board {
    /// Converts a `Vec<Vec<usize>>` into a `Board`.
    fn from(board: Vec<Vec<usize>>) -> Self {
        Self::new(board)
    }
}

impl From<Board> for Vec<Vec<usize>> {
    /// Converts a `Board` into a `Vec<Vec<usize>>`.
    fn from(board: Board) -> Self {
        board.0
    }
}

impl From<&Board> for Vec<Vec<usize>> {
    /// Converts a reference to a `Board` into a `Vec<Vec<usize>>` by cloning.
    fn from(board: &Board) -> Self {
        board.0.clone()
    }
}

impl<const N: usize> From<&[&[usize; N]; N]> for Board {
    /// Converts an array of references to fixed-size arrays into a `Board`.
    ///
    /// This is useful for creating a `Board` from statically defined Sudoku puzzles
    /// where rows are defined as separate arrays.
    fn from(board: &[&[usize; N]; N]) -> Self {
        Self::new(board.iter().map(|r| r.to_vec()).collect())
    }
}

/// An example 4x4 Sudoku puzzle. Values are 1-4, 0 for empty.
#[allow(dead_code)]
pub const EXAMPLE_FOUR: [[usize; 4]; 4] = [[2, 3, 0, 0], [4, 0, 0, 1], [0, 1, 2, 0], [0, 0, 0, 0]];

/// An example 9x9 Sudoku puzzle. Values are 1-9, 0 for empty.
#[allow(dead_code)]
pub const EXAMPLE_NINE: [[usize; 9]; 9] = [
    [5, 3, 0, 0, 7, 0, 0, 0, 0],
    [6, 0, 0, 1, 9, 5, 0, 0, 0],
    [0, 9, 8, 0, 0, 0, 0, 6, 0],
    [8, 0, 0, 0, 6, 0, 0, 0, 3],
    [4, 0, 0, 8, 0, 3, 0, 0, 1],
    [7, 0, 0, 0, 2, 0, 0, 0, 6],
    [0, 6, 0, 0, 0, 0, 2, 8, 0],
    [0, 0, 0, 4, 1, 9, 0, 0, 5],
    [0, 0, 0, 0, 8, 0, 0, 7, 9],
];

/// An example 16x16 Sudoku puzzle. Values are 1-16, 0 for empty.
#[allow(dead_code)]
pub const EXAMPLE_SIXTEEN: [[usize; 16]; 16] = [
    [0, 11, 0, 0, 0, 2, 3, 14, 0, 0, 9, 12, 0, 0, 0, 16],
    [15, 12, 0, 0, 0, 11, 0, 1, 13, 10, 0, 0, 0, 0, 7, 2],
    [0, 0, 10, 0, 0, 0, 0, 0, 16, 11, 0, 1, 6, 4, 12, 3],
    [0, 16, 14, 1, 0, 4, 0, 6, 0, 3, 0, 15, 0, 8, 0, 0],
    [1, 6, 5, 12, 0, 0, 11, 0, 0, 9, 8, 0, 0, 0, 0, 0],
    [0, 0, 0, 7, 14, 1, 8, 0, 0, 15, 6, 0, 13, 5, 0, 4],
    [4, 15, 8, 0, 9, 13, 0, 0, 0, 0, 7, 16, 3, 0, 0, 0],
    [0, 9, 13, 0, 0, 0, 0, 15, 10, 0, 0, 0, 7, 6, 0, 11],
    [14, 0, 6, 11, 0, 0, 0, 12, 7, 0, 0, 0, 0, 3, 13, 0],
    [0, 0, 0, 5, 8, 14, 0, 0, 0, 0, 13, 11, 0, 1, 2, 6],
    [13, 0, 16, 4, 0, 15, 5, 0, 0, 1, 12, 6, 8, 0, 0, 0],
    [0, 0, 0, 0, 0, 16, 10, 0, 0, 8, 0, 0, 11, 9, 4, 5],
    [0, 0, 11, 0, 1, 0, 14, 0, 5, 0, 3, 0, 15, 7, 16, 0],
    [5, 13, 15, 3, 16, 0, 4, 7, 0, 0, 0, 0, 0, 2, 0, 0],
    [16, 1, 0, 0, 0, 0, 12, 2, 14, 0, 15, 0, 0, 0, 3, 8],
    [9, 0, 0, 0, 13, 5, 0, 0, 8, 6, 16, 0, 0, 0, 10, 0],
];

/// An example 25x25 Sudoku puzzle. Values are 1-25, 0 for empty.
#[allow(dead_code)]
pub const EXAMPLE_TWENTY_FIVE: [[usize; 25]; 25] = [
    [
        0, 2, 0, 0, 0, 3, 14, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 13, 4, 24, 0, 7, 1, 0, 0,
    ],
    [
        0, 10, 17, 0, 0, 0, 6, 18, 0, 0, 22, 16, 0, 12, 0, 0, 0, 0, 1, 0, 0, 0, 13, 19, 0,
    ],
    [
        0, 15, 24, 13, 7, 0, 0, 0, 4, 0, 10, 0, 0, 3, 14, 0, 18, 0, 0, 0, 0, 22, 2, 6, 0,
    ],
    [
        0, 0, 1, 21, 0, 0, 15, 0, 22, 0, 0, 19, 13, 0, 0, 0, 8, 0, 0, 0, 0, 16, 18, 20, 0,
    ],
    [
        0, 5, 0, 0, 20, 7, 25, 19, 0, 0, 0, 21, 17, 18, 2, 10, 12, 22, 9, 15, 11, 0, 0, 0, 0,
    ],
    [
        11, 0, 0, 0, 22, 8, 0, 24, 7, 1, 5, 0, 0, 0, 13, 16, 17, 25, 23, 2, 4, 0, 6, 0, 19,
    ],
    [
        16, 9, 12, 0, 17, 0, 19, 22, 0, 0, 0, 0, 18, 21, 0, 0, 20, 6, 13, 0, 7, 0, 0, 23, 11,
    ],
    [
        0, 0, 6, 0, 21, 9, 16, 0, 3, 0, 0, 22, 20, 19, 0, 0, 0, 0, 15, 8, 25, 0, 0, 0, 0,
    ],
    [
        0, 0, 23, 5, 0, 2, 0, 0, 11, 17, 8, 0, 0, 0, 16, 12, 9, 0, 0, 21, 0, 3, 10, 0, 0,
    ],
    [
        0, 0, 0, 0, 0, 6, 0, 0, 12, 0, 9, 1, 25, 0, 3, 0, 11, 0, 0, 7, 0, 0, 21, 0, 0,
    ],
    [
        0, 0, 9, 0, 0, 23, 0, 5, 17, 4, 16, 0, 11, 0, 22, 18, 2, 0, 21, 13, 0, 0, 7, 0, 0,
    ],
    [
        4, 6, 0, 0, 5, 0, 0, 2, 0, 0, 0, 18, 21, 24, 0, 0, 19, 3, 0, 12, 23, 0, 0, 17, 0,
    ],
    [
        0, 0, 0, 12, 11, 0, 7, 3, 0, 24, 17, 20, 15, 13, 19, 1, 0, 5, 8, 0, 6, 9, 0, 0, 0,
    ],
    [
        0, 22, 0, 0, 14, 19, 0, 6, 16, 0, 0, 8, 9, 7, 0, 0, 0, 24, 0, 0, 3, 0, 0, 1, 18,
    ],
    [
        0, 0, 21, 0, 0, 25, 13, 0, 20, 8, 12, 0, 14, 0, 10, 9, 16, 15, 0, 6, 0, 0, 4, 0, 0,
    ],
    [
        0, 0, 25, 0, 0, 24, 0, 0, 18, 0, 4, 0, 3, 10, 5, 0, 1, 0, 0, 14, 0, 0, 0, 0, 0,
    ],
    [
        0, 0, 5, 3, 0, 17, 0, 0, 23, 7, 13, 0, 0, 0, 18, 19, 21, 0, 0, 22, 0, 11, 12, 0, 0,
    ],
    [
        0, 0, 0, 0, 18, 10, 8, 0, 0, 0, 0, 25, 23, 2, 0, 0, 5, 0, 16, 11, 9, 0, 3, 0, 0,
    ],
    [
        17, 20, 0, 0, 2, 0, 22, 16, 6, 0, 0, 7, 12, 0, 0, 0, 0, 9, 3, 0, 18, 0, 23, 24, 25,
    ],
    [
        6, 0, 4, 0, 16, 1, 11, 12, 25, 3, 19, 0, 0, 0, 21, 17, 23, 8, 0, 18, 2, 0, 0, 0, 14,
    ],
    [
        0, 0, 0, 0, 4, 14, 24, 11, 19, 23, 21, 17, 16, 8, 0, 0, 0, 1, 2, 9, 13, 0, 0, 5, 0,
    ],
    [
        0, 1, 14, 23, 0, 0, 0, 0, 9, 0, 0, 0, 19, 5, 0, 0, 24, 0, 12, 0, 0, 8, 17, 0, 0,
    ],
    [
        0, 16, 11, 8, 0, 0, 0, 0, 1, 0, 6, 4, 0, 0, 23, 0, 15, 0, 0, 0, 14, 12, 9, 10, 0,
    ],
    [
        0, 21, 3, 0, 0, 0, 17, 0, 0, 0, 0, 15, 0, 25, 20, 0, 0, 4, 10, 0, 0, 0, 16, 11, 0,
    ],
    [
        0, 0, 20, 2, 0, 16, 5, 8, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 19, 25, 0, 0, 0, 3, 0,
    ],
];

/// Represents the supported sizes of a Sudoku board (N x N).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Size {
    /// A 4x4 Sudoku board.
    Four = 4,
    /// A 9x9 Sudoku board.
    Nine = 9,
    /// A 16x16 Sudoku board.
    Sixteen = 16,
    /// A 25x25 Sudoku board.
    TwentyFive = 25,
}

impl TryFrom<usize> for Size {
    type Error = ();

    /// Tries to convert a `usize` into a `Size`.
    ///
    /// Returns `Ok(Size)` if the value is one of 4, 9, 16, or 25.
    /// Otherwise, returns `Err(())`.
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        match value {
            4 => Ok(Self::Four),
            9 => Ok(Self::Nine),
            16 => Ok(Self::Sixteen),
            25 => Ok(Self::TwentyFive),
            _ => Err(()),
        }
    }
}

impl From<Size> for usize {
    /// Converts a `Size` into its `usize` representation.
    fn from(size: Size) -> Self {
        match size {
            Size::Four => 4,
            Size::Nine => 9,
            Size::Sixteen => 16,
            Size::TwentyFive => 25,
        }
    }
}

impl Display for Size {
    /// Formats the size as `NxN`. For example, `Size::Nine` will be "9x9".
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let size: usize = (*self).into();
        write!(f, "{size}x{size}")
    }
}

/// Represents a Sudoku puzzle, including its board and size.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sudoku {
    /// The game board.
    pub board: Board,
    /// The dimension of the Sudoku grid (e.g. 9 for a 9x9 grid).
    pub size: Size,
}

impl Display for Sudoku {
    /// Formats the Sudoku puzzle, including its size and board.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Sudoku {{ size: {} }}", self.size)?;
        write!(f, "{}", self.board)
    }
}

/// Represents a variable in the SAT encoding of a Sudoku puzzle.
///
/// A variable `(row, col, num)` is true if the cell at `(row, col)` contains `num`.
/// Rows, columns, and numbers are 1-indexed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Variable {
    /// The row index (1-based).
    pub row: usize,
    /// The column index (1-based).
    pub col: usize,
    /// The number in the cell (1-based).
    pub num: usize,
}

impl Variable {
    /// Creates a new `Variable`.
    ///
    /// # Arguments
    ///
    /// * `row`: 1-based row index.
    /// * `col`: 1-based column index.
    /// * `num`: 1-based number.
    #[must_use]
    pub const fn new(row: usize, col: usize, num: usize) -> Self {
        Self { row, col, num }
    }

    /// Encodes the variable into a unique positive integer for SAT solvers.
    ///
    /// The encoding scheme maps `(row, col, num)` to a unique integer.
    /// Assumes `row`, `col`, `num` are 1-indexed and within the board's dimensions.
    /// The resulting integer is also 1-indexed.
    ///
    /// Formula: `((row - 1) * board_size^2) + ((col - 1) * board_size) + (num - 1) + 1`
    ///
    /// # Arguments
    ///
    /// * `size`: The `Size` of the Sudoku board.
    #[must_use]
    pub const fn encode(&self, size: Size) -> usize {
        let board_size = size as usize;
        let row = self.row;
        let col = self.col;
        let num = self.num;

        ((row - 1) * board_size * board_size + (col - 1) * board_size + (num - 1)) + 1
    }
}

impl Size {
    /// Returns the size of the blocks (subgrids) in a Sudoku puzzle.
    /// For example, a 9x9 Sudoku has 3x3 blocks.
    #[must_use]
    pub const fn block_size(self) -> usize {
        match self {
            Self::Four => 2,
            Self::Nine => 3,
            Self::Sixteen => 4,
            Self::TwentyFive => 5,
        }
    }
}

/// Generates SAT clauses ensuring each cell contains at least one number.
/// (`X_r,c,1` OR `X_r,c,2` OR ... OR `X_r,c,N`) for each cell (r,c).
fn generate_cell_clauses(size: usize) -> Vec<Vec<i32>> {
    let mut clauses = vec![];
    for row in 1..=size {
        for col in 1..=size {
            let clause = (1..=size)
                .map(|num| {
                    i32::try_from(
                        Variable::new(row, col, num)
                            .encode(Size::try_from(size).expect("Invalid size")),
                    )
                    .expect("Invalid variable")
                })
                .collect();

            clauses.push(clause);
        }
    }
    clauses
}

/// Generates SAT clauses ensuring no number appears more than once in each row.
/// (-`X_r,c1,k` OR -`X_r,c2,k`) for each row r, number k, and pair of columns c1 < c2.
fn generate_row_clauses(size: usize) -> Vec<Vec<i32>> {
    let mut clauses = vec![];
    for row in 1..=size {
        for num in 1..=size {
            for col1 in 1..=size {
                for col2 in (col1 + 1)..=size {
                    if col1 > col2 {
                        continue;
                    }

                    let var1 = Variable::new(row, col1, num);
                    let var2 = Variable::new(row, col2, num);

                    clauses.push(vec![
                        -i32::try_from(var1.encode(Size::try_from(size).expect("Invalid size")))
                            .expect("Invalid variable"),
                        -i32::try_from(var2.encode(Size::try_from(size).expect("Invalid size")))
                            .expect("Invalid variable"),
                    ]);
                }
            }
        }
    }
    clauses
}

/// Generates SAT clauses ensuring no number appears more than once in each column.
/// (-`X_r1,c,k` OR -`X_r2,c,k`) for each column c, number k, and pair of rows r1 < r2.
fn generate_col_clauses(size: usize) -> Vec<Vec<i32>> {
    let mut clauses = vec![];
    for col in 1..=size {
        for num in 1..=size {
            for row1 in 1..=size {
                for row2 in (row1 + 1)..=size {
                    let var1 = Variable::new(row1, col, num);
                    let var2 = Variable::new(row2, col, num);

                    clauses.push(vec![
                        -i32::try_from(var1.encode(Size::try_from(size).expect("Invalid size")))
                            .expect("Invalid variable"),
                        -i32::try_from(var2.encode(Size::try_from(size).expect("Invalid size")))
                            .expect("Invalid variable"),
                    ]);
                }
            }
        }
    }
    clauses
}

/// Generates SAT clauses ensuring no number appears more than once in each block (subgrid).
/// (-`X_r1,c1,k` OR -`X_r2,c2,k`) for each number k and pair of distinct cells (r1,c1), (r2,c2) within the same block.
fn generate_block_clauses(board_size: usize, block_size: usize) -> Vec<Vec<i32>> {
    let mut clauses = Vec::new();
    for n in 1..=board_size {
        for br_start_idx in (0..board_size).step_by(block_size) {
            for bc_start_idx in (0..board_size).step_by(block_size) {
                let mut block_cells = Vec::new();
                for r_offset in 0..block_size {
                    for c_offset in 0..block_size {
                        block_cells
                            .push((br_start_idx + r_offset + 1, bc_start_idx + c_offset + 1));
                    }
                }

                for i in 0..block_cells.len() {
                    for j in i + 1..block_cells.len() {
                        let (r1, c1) = block_cells[i];
                        let (r2, c2) = block_cells[j];
                        let var1 = Variable::new(r1, c1, n);
                        let var2 = Variable::new(r2, c2, n);

                        clauses.push(vec![
                            -i32::try_from(
                                var1.encode(Size::try_from(board_size).expect("Invalid size")),
                            )
                            .expect("Invalid variable"),
                            -i32::try_from(
                                var2.encode(Size::try_from(board_size).expect("Invalid size")),
                            )
                            .expect("Invalid variable"),
                        ]);
                    }
                }
            }
        }
    }
    clauses
}

/// Generates SAT clauses for the pre-filled cells in the Sudoku board.
/// (`X_r,c,k`) for each cell (r,c) pre-filled with k.
fn generate_pre_filled_clauses(size: usize, board: &Board) -> Vec<Vec<i32>> {
    let mut clauses = vec![];
    for (r_idx, row_vec) in board.0.iter().enumerate() {
        for (c_idx, &n_val) in row_vec.iter().enumerate() {
            if n_val != 0 {
                let var = Variable::new(r_idx + 1, c_idx + 1, n_val);
                clauses.push(vec![
                    i32::try_from(var.encode(Size::try_from(size).expect("Invalid size")))
                        .expect("Invalid variable"),
                ]);
            }
        }
    }
    clauses
}

impl Sudoku {
    /// Creates a new `Sudoku` puzzle from a `Board`.
    ///
    /// The size of the Sudoku is inferred from the dimensions of the board.
    ///
    /// # Panics
    ///
    /// Panics if the board dimensions do not correspond to a supported `Size`
    /// (e.g. if `board.0.len()` is not 4, 9, 16, or 25).
    #[must_use]
    pub fn new(board: Board) -> Self {
        let size_val = board.0.len();
        Self {
            board,
            size: Size::try_from(size_val).expect("Invalid size for Sudoku board"),
        }
    }

    /// Decodes a `Sudoku` solution from SAT solver results.
    ///
    /// Given a `Solutions` object (typically from a SAT solver), this method
    /// constructs the solved Sudoku board by checking which SAT variables `X_r,c,k` are true.
    ///
    /// # Arguments
    ///
    /// * `solutions`: A `Solutions` object containing the truth assignments for SAT variables.
    ///
    /// # Returns
    ///
    /// A new `Sudoku` instance representing the solved puzzle.
    ///
    /// # Panics
    /// if `var.encode(self.size)` results in 0, as `NonZeroI32::new` would return `None`.
    /// However, `Variable::encode` is designed to return positive integers.
    #[must_use]
    pub fn decode(&self, solutions: &Solutions) -> Self {
        let size_val: usize = self.size.into();
        let mut board_vec = vec![vec![0; size_val]; size_val];
        for row in 1..=size_val {
            for col in 1..=size_val {
                for num in 1..=size_val {
                    let var = Variable::new(row, col, num);
                    #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
                    let encoded_var = NonZeroI32::new(var.encode(self.size) as i32)
                        .expect("Encoded variable should not be zero");
                    if solutions.check(encoded_var) {
                        board_vec[row - 1][col - 1] = num;
                    }
                }
            }
        }
        Self {
            board: Board::new(board_vec),
            size: self.size,
        }
    }

    /// Converts the Sudoku puzzle into Conjunctive Normal Form (CNF) for a SAT solver.
    ///
    /// This method generates all the necessary clauses to represent the Sudoku problem:
    /// 1. Cell constraints: Each cell must contain at least one number.
    /// 2. Row constraints: Each number must appear at most once per row.
    /// 3. Column constraints: Each number must appear at most once per column.
    /// 4. Block constraints: Each number must appear at most once per block (subgrid).
    /// 5. Pre-filled constraints: Given numbers in the puzzle are fixed (unit clauses).
    ///
    /// The combination of "at least one" (from cell constraints) and "at most one"
    /// (from row, col, block constraints for each number-pair in a cell) ensures each cell
    /// contains exactly one number.
    ///
    /// # Type Parameters
    ///
    /// * `L`: A type that implements the `Literal` trait from the SAT solver crate.
    /// * `S`: A type that implements the `LiteralStorage<L>` trait from the SAT solver crate.
    ///
    /// # Returns
    ///
    /// A `Cnf<L, S>` object representing the Sudoku puzzle in CNF.
    ///
    /// # Panics
    /// Panics if `Size::try_from` or `i32::try_from` fails during clause generation,
    /// which could happen if variable encodings produce values too large for `i32`
    /// or if `size` is not a supported Sudoku dimension (though `self.size` should always be valid).
    #[must_use]
    pub fn to_cnf<L: Literal, S: LiteralStorage<L>>(&self) -> Cnf<L, S> {
        let size_val = self.size as usize;
        let block_size_val = self.size.block_size();

        let cell_clauses = generate_cell_clauses(size_val);
        let row_clauses = generate_row_clauses(size_val);
        let col_clauses = generate_col_clauses(size_val);
        let block_clauses = generate_block_clauses(size_val, block_size_val);
        let pre_filled_clauses = generate_pre_filled_clauses(size_val, &self.board);

        let clauses: Vec<Vec<i32>> = cell_clauses
            .into_iter()
            .chain(row_clauses)
            .chain(col_clauses)
            .chain(block_clauses)
            .chain(pre_filled_clauses)
            .collect();

        Cnf::new(clauses)
    }

    /// Returns an iterator over the rows of the Sudoku board.
    /// Each item yielded by the iterator is a `Vec<usize>` representing a row.
    pub fn iter(&self) -> impl Iterator<Item = Vec<usize>> {
        self.board.0.clone().into_iter()
    }

    /// Parses a `Sudoku` from a string representation.
    ///
    /// See [`parse_sudoku`] for details on the expected format and behavior.
    ///
    /// # Arguments
    ///
    /// * `sudoku_str`: A string slice representing the Sudoku.
    ///
    /// # Errors
    ///
    /// Returns `Err(String)` if the string format is invalid.
    pub fn from_string(sudoku_str: &str) -> Result<Self, String> {
        parse_sudoku(sudoku_str)
    }

    /// Parses a `Sudoku` from a file.
    ///
    /// See [`parse_sudoku_file`] for details.
    ///
    /// # Arguments
    ///
    /// * `file_path`: Path to the file containing the Sudoku representation.
    ///
    /// # Errors
    ///
    /// Returns `Err(String)` if the file cannot be read, or if its content
    /// is an invalid Sudoku representation.
    pub fn from_file(file_path: &PathBuf) -> Result<Self, String> {
        parse_sudoku_file(file_path)
    }
}

impl From<Board> for Sudoku {
    /// Converts a `Board` into a `Sudoku` puzzle.
    /// Size is inferred from the board.
    /// # Panics
    /// Panics if the board size is not one of the supported `Size` values.
    fn from(board: Board) -> Self {
        Self::new(board)
    }
}

impl From<Sudoku> for Board {
    /// Converts a `Sudoku` puzzle into its `Board` representation.
    fn from(sudoku: Sudoku) -> Self {
        sudoku.board
    }
}

/// Parses a Sudoku puzzle from a string.
///
/// The input string should ideally have `N` lines, each containing `N` space-separated numbers,
/// where `N` is a supported Sudoku size (4, 9, 16, 25). `0` represents an empty cell.
///
/// Behavior details:
/// - The number of lines in the input string determines the `size` of the Sudoku. This includes empty lines.
/// - If `size` is not a supported Sudoku dimension (4, 9, 16, 25), `Sudoku::new` called at the end will panic.
/// - Empty lines are skipped during parsing; corresponding rows in the board will remain all zeros.
/// - If a line contains more numbers than `size`, `board[i][j]` access will panic.
/// - If a line contains fewer numbers than `size`, the remaining cells in that row are treated as empty (0).
/// - Non-numeric tokens or numbers greater than `size` will result in an error.
///
/// # Arguments
///
/// * `sudoku_str`: The string representation of the Sudoku.
///
/// # Returns
///
/// `Ok(Sudoku)` if parsing is successful (before the potential panic in `Sudoku::new`).
/// `Err(String)` if invalid characters or out-of-range numbers are found.
///
/// # Panics
/// - If a line has more items than `size` (due to `board[i][j]` out-of-bounds access).
/// - If `size` (derived from `lines.len()`) is not a supported Sudoku size (4, 9, 16, 25),
///   this function will return `Ok(Sudoku)` but the caller might panic if `Sudoku::new` (called internally) panics.
///
/// # Errors
///
/// Returns `Err(String)` if the input string is not a valid Sudoku representation,
pub fn parse_sudoku(sudoku: &str) -> Result<Sudoku, String> {
    let lines = sudoku.lines().collect_vec();
    let size = lines.len();
    let mut board = vec![vec![0; size]; size];

    for (i, line) in lines.iter().enumerate() {
        if line.is_empty() {
            continue;
        }
        for (j, c) in line.split_ascii_whitespace().enumerate() {
            if j >= size {
                return Err(format!(
                    "Invalid Sudoku: Too many numbers in line {}",
                    i + 1
                ));
            }

            if let Ok(num) = c.parse::<usize>() {
                if num > size {
                    return Err(format!("Invalid Sudoku: Number {num} exceeds size {size}"));
                }
                board[i][j] = num;
            } else {
                return Err(format!("Invalid Sudoku: Invalid character {c}"));
            }
        }
    }

    Ok(Sudoku::new(Board::new(board)))
}

/// Parses a Sudoku puzzle from a file.
///
/// Reads the file content and uses `parse_sudoku` to parse it.
/// Refer to [`parse_sudoku`] for details on parsing behavior and potential panics.
///
/// # Arguments
///
/// * `file_path`: The path to the file.
///
/// # Returns
///
/// `Ok(Sudoku)` if file reading and parsing are successful.
/// `Err(String)` if the file cannot be read or its content is invalid according to `parse_sudoku`.
///
/// # Panics
/// Under the same conditions as `parse_sudoku` (e.g. invalid size, too many numbers per line).
///
/// # Errors
/// Returns `Err(String)` if the file cannot be read or if its content is not a valid Sudoku representation.
pub fn parse_sudoku_file(file_path: &PathBuf) -> Result<Sudoku, String> {
    let content = std::fs::read_to_string(file_path).map_err(|e| e.to_string())?;
    parse_sudoku(&content)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    #[test]
    fn board_new_and_display() {
        let data = vec![vec![1, 0], vec![0, 2]];
        let board = Board::new(data.clone());
        assert_eq!(board.0, data);
        assert_eq!(format!("{board}"), "1 0\n0 2\n");
    }

    #[test]
    fn board_from_vec_vec() {
        let data = vec![vec![1], vec![2]];
        let board: Board = data.clone().into();
        assert_eq!(board.0, data);
    }

    #[test]
    fn vec_vec_from_board() {
        let data = vec![vec![1], vec![2]];
        let board = Board::new(data.clone());
        let converted_data: Vec<Vec<usize>> = board.into();
        assert_eq!(converted_data, data);
    }

    #[test]
    fn vec_vec_from_ref_board() {
        let data = vec![vec![1], vec![2]];
        let board = Board::new(data.clone());
        let converted_data: Vec<Vec<usize>> = (&board).into();
        assert_eq!(converted_data, data);
    }

    #[test]
    fn board_from_array_of_refs() {
        let r1: [usize; 2] = [1, 0];
        let r2: [usize; 2] = [0, 2];
        let board_data: [&[usize; 2]; 2] = [&r1, &r2];
        let board = Board::from(&board_data);
        assert_eq!(board, Board::new(vec![vec![1, 0], vec![0, 2]]));
    }

    #[test]
    fn size_try_from_usize() {
        assert_eq!(Size::try_from(4), Ok(Size::Four));
        assert_eq!(Size::try_from(9), Ok(Size::Nine));
        assert_eq!(Size::try_from(16), Ok(Size::Sixteen));
        assert_eq!(Size::try_from(25), Ok(Size::TwentyFive));
        assert_eq!(Size::try_from(1), Err(()));
        assert_eq!(Size::try_from(0), Err(()));
    }

    #[test]
    fn usize_from_size() {
        assert_eq!(usize::from(Size::Four), 4);
        assert_eq!(usize::from(Size::Nine), 9);
        assert_eq!(usize::from(Size::Sixteen), 16);
        assert_eq!(usize::from(Size::TwentyFive), 25);
    }

    #[test]
    fn size_display() {
        assert_eq!(format!("{}", Size::Four), "4x4");
        assert_eq!(format!("{}", Size::Nine), "9x9");
    }

    #[test]
    fn size_block_size() {
        assert_eq!(Size::Four.block_size(), 2);
        assert_eq!(Size::Nine.block_size(), 3);
        assert_eq!(Size::Sixteen.block_size(), 4);
        assert_eq!(Size::TwentyFive.block_size(), 5);
    }

    #[test]
    fn variable_new_and_encode() {
        let var = Variable::new(1, 1, 1);
        assert_eq!(
            var,
            Variable {
                row: 1,
                col: 1,
                num: 1
            }
        );

        assert_eq!(Variable::new(1, 1, 1).encode(Size::Four), 1); // (0*16) + (0*4) + 0 + 1 = 1
        assert_eq!(Variable::new(1, 1, 4).encode(Size::Four), 4); // (0*16) + (0*4) + 3 + 1 = 4
        assert_eq!(Variable::new(1, 2, 1).encode(Size::Four), 5); // (0*16) + (1*4) + 0 + 1 = 5
        assert_eq!(Variable::new(2, 1, 1).encode(Size::Four), 17); // (1*16) + (0*4) + 0 + 1 = 17
        assert_eq!(Variable::new(4, 4, 4).encode(Size::Four), 64); // (3*16) + (3*4) + 3 + 1 = 48+12+3+1 = 64

        assert_eq!(Variable::new(1, 1, 1).encode(Size::Nine), 1);
        assert_eq!(Variable::new(9, 9, 9).encode(Size::Nine), 729); // (8*81) + (8*9) + 8 + 1 = 648+72+8+1 = 729
    }

    // Test Sudoku
    #[test]
    fn sudoku_new() {
        let board_data = vec![vec![0; 4]; 4];
        let board = Board::new(board_data);
        let sudoku = Sudoku::new(board.clone());
        assert_eq!(sudoku.board, board);
        assert_eq!(sudoku.size, Size::Four);
    }

    #[test]
    #[should_panic(expected = "Invalid size for Sudoku board")]
    fn sudoku_new_invalid_size() {
        let board_data = vec![vec![0; 5]; 5];
        let board = Board::new(board_data);
        let _ = Sudoku::new(board);
    }

    #[test]
    fn sudoku_display() {
        let board_data = vec![
            vec![1, 0, 0, 0],
            vec![0, 2, 0, 0],
            vec![0, 0, 3, 0],
            vec![0, 0, 0, 4],
        ];
        let sudoku = Sudoku::new(Board::new(board_data));
        let expected_display = "Sudoku { size: 4x4 }\n1 0 0 0\n0 2 0 0\n0 0 3 0\n0 0 0 4\n";
        assert_eq!(format!("{sudoku}"), expected_display);
    }

    #[test]
    fn sudoku_iter() {
        let sudoku_board_data = vec![
            vec![1, 2, 0, 0],
            vec![3, 4, 0, 0],
            vec![0, 0, 0, 0],
            vec![0, 0, 0, 0],
        ];
        let sudoku = Sudoku::from(Board::from(sudoku_board_data));
        let mut iter = sudoku.iter();
        assert_eq!(iter.next(), Some(vec![1, 2, 0, 0]));
        assert_eq!(iter.next(), Some(vec![3, 4, 0, 0]));
        assert_eq!(iter.next(), Some(vec![0, 0, 0, 0]));
        assert_eq!(iter.next(), Some(vec![0, 0, 0, 0]));
        assert_eq!(iter.next(), None);
    }

    // Test parsing
    #[test]
    fn parse_sudoku_valid_4x4() {
        let s = "1 0 3 0\n0 2 0 0\n0 0 0 4\n0 0 1 0";
        let sudoku = parse_sudoku(s).unwrap();
        assert_eq!(sudoku.size, Size::Four);
        let expected_board = Board::new(vec![
            vec![1, 0, 3, 0],
            vec![0, 2, 0, 0],
            vec![0, 0, 0, 4],
            vec![0, 0, 1, 0],
        ]);
        assert_eq!(sudoku.board, expected_board);
    }

    #[test]
    #[should_panic(expected = "Invalid size for Sudoku board")]
    fn parse_sudoku_invalid_size_panic() {
        let s = "1 0\n0 1";
        parse_sudoku(s).unwrap();
    }

    #[test]
    fn parse_sudoku_invalid_char() {
        let s = "1 0 X 0\n0 2 0 0\n0 0 0 4\n0 0 1 0";
        assert!(parse_sudoku(s).is_err());
        assert_eq!(
            parse_sudoku(s).unwrap_err(),
            "Invalid Sudoku: Invalid character X"
        );
    }

    #[test]
    fn parse_sudoku_number_too_large() {
        let s = "1 0 5 0\n0 2 0 0\n0 0 0 4\n0 0 1 0"; // 5 in a 4x4
        let err = parse_sudoku(s).unwrap_err();
        assert_eq!(err, "Invalid Sudoku: Number 5 exceeds size 4");
    }

    #[test]
    fn parse_sudoku_too_many_numbers_in_line() {
        let s = "1 0 0 0 5\n0 2 0 0\n0 0 0 4\n0 0 1 0";
        match parse_sudoku(s) {
            Ok(_) => panic!("Should have failed or panicked."),
            Err(e) => {
                assert_eq!(e, "Invalid Sudoku: Too many numbers in line 1");
            }
        }
    }

    #[test]
    fn parse_sudoku_too_few_numbers_in_line() {
        let s = "1 0\n0 2 0 0\n0 0 0 4\n0 0 1 0";
        let sudoku = parse_sudoku(s).unwrap();
        let expected_board = Board::new(vec![
            vec![1, 0, 0, 0], // 1 0 -> 1 0 0 0
            vec![0, 2, 0, 0],
            vec![0, 0, 0, 4],
            vec![0, 0, 1, 0],
        ]);
        assert_eq!(sudoku.board, expected_board);
    }

    #[test]
    fn parse_sudoku_empty_line_behavior() {
        let s = "1 0 3 0\n0 2 0 0\n\n0 0 0 4\n0 0 1 0";
        assert!(
            std::panic::catch_unwind(|| parse_sudoku(s)).is_err(),
            "Sudoku::new should panic for size 5"
        );
    }

    #[test]
    fn sudoku_decode_basic() {
        let initial_board_data = vec![vec![0; 4]; 4];
        let sudoku = Sudoku::new(Board::new(initial_board_data));

        let mut solution_vars = Vec::new();
        let solution_grid: [[usize; 4]; 4] =
            [[1, 2, 3, 4], [3, 4, 1, 2], [2, 1, 4, 3], [4, 3, 2, 1]];

        for (r, row) in solution_grid.iter().enumerate() {
            for c in 0..4 {
                let num = row[c];
                #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
                solution_vars.push(Variable::new(r + 1, c + 1, num).encode(Size::Four) as i32);
            }
        }

        let solutions = Solutions::new(&solution_vars);
        let decoded_sudoku = sudoku.decode(&solutions);

        let expected_board_data: Vec<Vec<usize>> =
            solution_grid.iter().map(|row| row.to_vec()).collect();
        assert_eq!(decoded_sudoku.board.0, expected_board_data);
        assert_eq!(decoded_sudoku.size, Size::Four);
    }

    #[test]
    fn test_generate_cell_clauses_content() {
        let cell_clauses = generate_cell_clauses(4);
        let clause_for_cell_1_1 = vec![1, 2, 3, 4];
        assert!(cell_clauses.contains(&clause_for_cell_1_1));
        assert_eq!(cell_clauses.len(), 4 * 4);
    }

    #[test]
    fn test_generate_row_clauses_content() {
        let row_clauses = generate_row_clauses(4);
        #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
        let var111 = Variable::new(1, 1, 1).encode(Size::Four) as i32;
        #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
        let var121 = Variable::new(1, 2, 1).encode(Size::Four) as i32;
        let clause_example = vec![-var111, -var121]; // {-1, -5}
        assert!(row_clauses.contains(&clause_example));
        assert_eq!(row_clauses.len(), 96);
    }

    #[test]
    fn test_generate_pre_filled_clauses() {
        let board_data = vec![
            vec![1, 0, 0, 0],
            vec![0, 2, 0, 0],
            vec![0, 0, 0, 0],
            vec![0, 0, 0, 0],
        ];
        let board = Board::new(board_data);
        let pre_filled = generate_pre_filled_clauses(4, &board);

        #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
        let var111 = Variable::new(1, 1, 1).encode(Size::Four) as i32;
        #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
        let var222 = Variable::new(2, 2, 2).encode(Size::Four) as i32;

        let expected_clauses: HashSet<Vec<i32>> =
            [vec![var111], vec![var222]].iter().cloned().collect();

        let actual_clauses: HashSet<Vec<i32>> = pre_filled.iter().cloned().collect();
        assert_eq!(actual_clauses, expected_clauses);
        assert_eq!(pre_filled.len(), 2);
    }
}

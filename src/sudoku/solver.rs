use crate::sat::assignment::Solutions;
use crate::sat::cnf::Cnf;
use crate::sat::literal::PackedLiteral;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Board(Vec<Vec<usize>>);

impl Board {
    #[must_use]
    pub const fn new(board: Vec<Vec<usize>>) -> Self {
        Self(board)
    }
}

impl From<Vec<Vec<usize>>> for Board {
    fn from(board: Vec<Vec<usize>>) -> Self {
        Self::new(board)
    }
}

impl From<Board> for Vec<Vec<usize>> {
    fn from(board: Board) -> Self {
        board.0
    }
}

impl From<&Board> for Vec<Vec<usize>> {
    fn from(board: &Board) -> Self {
        board.0.clone()
    }
}

impl From<[Vec<usize>; 4]> for Board {
    fn from(board: [Vec<usize>; 4]) -> Self {
        Self::new(board.to_vec())
    }
}

impl From<[Vec<usize>; 9]> for Board {
    fn from(board: [Vec<usize>; 9]) -> Self {
        Self::new(board.to_vec())
    }
}

impl From<[Vec<usize>; 16]> for Board {
    fn from(board: [Vec<usize>; 16]) -> Self {
        Self::new(board.to_vec())
    }
}

impl From<[Vec<usize>; 25]> for Board {
    fn from(board: [Vec<usize>; 25]) -> Self {
        Self::new(board.to_vec())
    }
}

impl From<&[&[usize; 4]; 4]> for Board {
    fn from(board: &[&[usize; 4]; 4]) -> Self {
        Self::new(board.iter().map(|r| r.to_vec()).collect())
    }
}

impl From<&[&[usize; 9]; 9]> for Board {
    fn from(board: &[&[usize; 9]; 9]) -> Self {
        Self::new(board.iter().map(|r| r.to_vec()).collect())
    }
}

impl From<&[&[usize; 16]; 16]> for Board {
    fn from(board: &[&[usize; 16]; 16]) -> Self {
        Self::new(board.iter().map(|r| r.to_vec()).collect())
    }
}

impl From<&[&[usize; 25]; 25]> for Board {
    fn from(board: &[&[usize; 25]; 25]) -> Self {
        Self::new(board.iter().map(|r| r.to_vec()).collect())
    }
}

pub const EXAMPLE_FOUR: [[usize; 4]; 4] = [[5, 3, 0, 0], [6, 0, 0, 1], [0, 9, 8, 0], [0, 0, 0, 0]];

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

#[derive(Debug, Clone, PartialEq, Eq, Copy, PartialOrd, Ord, Hash)]
pub enum Size {
    Four = 4,
    Nine = 9,
    Sixteen = 16,
    TwentyFive = 25,
}

impl TryFrom<usize> for Size {
    type Error = ();

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
    fn from(size: Size) -> Self {
        match size {
            Size::Four => 4,
            Size::Nine => 9,
            Size::Sixteen => 16,
            Size::TwentyFive => 25,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sudoku {
    pub board: Board,
    pub size: Size,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Variable {
    pub row: usize,
    pub col: usize,
    pub num: usize,
}

impl Variable {
    #[must_use]
    pub const fn new(row: usize, col: usize, num: usize) -> Self {
        Self { row, col, num }
    }

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

fn generate_col_clauses(size: usize) -> Vec<Vec<i32>> {
    let mut clauses = vec![];
    for col in 1..=size {
        for num in 1..=size {
            for row1 in 1..=size {
                for row2 in (row1 + 1)..=size {
                    if row1 > row2 {
                        continue;
                    }
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

fn generate_block_clauses(board_size: usize, block_size: usize) -> Vec<Vec<i32>> {
    let mut clauses = Vec::new();
    for n in 1..=board_size {
        for br in (0..board_size).step_by(block_size) {
            for bc in (0..board_size).step_by(block_size) {
                let mut block_cells = Vec::new();
                for r in br + 1..=br + block_size {
                    for c in bc + 1..=bc + block_size {
                        block_cells.push((r, c));
                    }
                }
                for i in 0..block_cells.len() {
                    for j in i + 1..block_cells.len() {
                        let (r1, c1) = block_cells[i];
                        let (r2, c2) = block_cells[j];
                        let var1 = Variable::new(r1, c1, n);
                        let var2 = Variable::new(r2, c2, n);
                        if (r1, c1) > (r2, c2) {
                            continue;
                        }
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

fn generate_pre_filled_clauses(size: usize, board: &Board) -> Vec<Vec<i32>> {
    let mut clauses = vec![];
    for (r, row) in board.0.iter().enumerate() {
        for (c, &n) in row.iter().enumerate() {
            if n != 0 {
                let var = Variable::new(r + 1, c + 1, n);
                clauses.push(vec![i32::try_from(
                    var.encode(Size::try_from(size).expect("Invalid size")),
                )
                .expect("Invalid variable")]);
            }
        }
    }
    clauses
}

impl Sudoku {
    #[must_use]
    pub fn new(board: Board) -> Self {
        let size = board.0.len();
        Self {
            board,
            size: Size::try_from(size).expect("Invalid size"),
        }
    }

    #[must_use]
    pub fn decode_solution(&self, solutions: &Solutions) -> Self {
        let size = self.size.into();
        let mut board = vec![vec![0; size]; size];
        for row in 1..=size {
            for col in 1..=size {
                for num in 1..=size {
                    let var = Variable::new(row, col, num);
                    #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
                    let encoded = var.encode(self.size) as i32;
                    if solutions.check(encoded) {
                        board[row - 1][col - 1] = num;
                    }
                }
            }
        }
        Self {
            board: Board::new(board),
            size: self.size,
        }
    }

    #[must_use]
    pub fn to_cnf(&self) -> Cnf<PackedLiteral, Vec<PackedLiteral>> {
        let size = self.size as usize;
        let block_size = self.size.block_size();

        let cell_clauses = generate_cell_clauses(size);
        let row_clauses = generate_row_clauses(size);
        let col_clauses = generate_col_clauses(size);
        let block_clauses = generate_block_clauses(size, block_size);
        let pre_filled_clauses = generate_pre_filled_clauses(size, &self.board);

        let clauses: Vec<Vec<i32>> = cell_clauses
            .into_iter()
            .chain(row_clauses)
            .chain(col_clauses)
            .chain(block_clauses)
            .chain(pre_filled_clauses)
            .collect();

        Cnf::new(clauses)
    }

    pub fn iter(&self) -> impl Iterator<Item = Vec<usize>> {
        self.board.0.clone().into_iter()
    }
}

impl From<Board> for Sudoku {
    fn from(board: Board) -> Self {
        Self::new(board)
    }
}

impl From<Sudoku> for Board {
    fn from(sudoku: Sudoku) -> Self {
        sudoku.board
    }
}

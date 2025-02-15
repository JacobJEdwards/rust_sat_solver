use crate::sat::assignment::VecAssignment;
use crate::sat::propagation::{PropagationQueue, PropagationStack};
use crate::sat::state::{Solver, State};
use crate::sudoku::solver::{Board, Sudoku, EXAMPLE_SIXTEEN, EXAMPLE_TWENTY_FIVE};

mod nonogram;
mod sat;
mod sudoku;

fn main() {
    // time

    let board = EXAMPLE_SIXTEEN
        .iter()
        .map(|x| x.to_vec())
        .collect::<Vec<_>>();

    let sudoku = Sudoku::new(Board::from(board));

    let cnf = sudoku.to_cnf();
    let mut state: State<VecAssignment, PropagationQueue> = State::new(cnf);

    let time = std::time::Instant::now();
    let sol = state.solve();
    let elapsed = time.elapsed();

    println!("Time: {:?}", elapsed);
    match sol {
        Some(sol) => {
            let solution = sudoku.decode_solution(&sol);

            for row in solution.iter() {
                println!("{:?}", row);
            }
        }
        None => println!("No solution"),
    }

    println!("\n\n");

    // match sol2 {
    //     Some(sol) => {
    //         let solution = sudoku.decode_solution(sol);
    //         for row in solution.iter() {
    //             println!("{:?}", row);
    //         }
    //     }
    //     None => println!("No solution"),
    // }
}

use crate::sudoku::solver::{Board, Sudoku, EXAMPLE_TWENTY_FIVE, EXAMPLE_SIXTEEN, EXAMPLE_NINE};

mod sat;
mod sudoku;

fn main() {
    // time
    let time = std::time::Instant::now();
    let board = Vec::from(EXAMPLE_SIXTEEN.iter().map(|x| x.to_vec()).collect::<Vec<_>>());
    let sudoku = Sudoku::new(Board::from(board));
    let cnf = sudoku.to_cnf();
    let clauses = cnf.clauses().iter().map(|c| sat::solver::Clause::new(c.literals.clone()))
        .collect::<Vec<_>>();
    let mut state = sat::state::State::new(&cnf);
   // let mut otherState = sat::solver::CDCL::new(clauses, 16);
    let sol = state.solve();
    //let sol2 = otherState.solve();
    let elapsed = time.elapsed();
    println!("Time: {:?}", elapsed);
    match sol {
        Some(sol) => {
            let solution = sudoku.decode_solution(sol);
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

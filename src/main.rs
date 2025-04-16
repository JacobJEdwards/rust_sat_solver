use crate::sat::cdcl::Cdcl;
use crate::sat::cnf::Cnf;
use crate::sat::dimacs::parse_file;
use crate::sat::solver::Solver;

mod nonogram;
mod sat;
mod smt;
mod sudoku;

#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

fn main() {
    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        let cnf = parse_file(&file).unwrap();
        let mut state: Cdcl = Solver::new(cnf.clone());
        let sol = state.solve();

        println!("{:?}", file);
        println!("{:?}", sol);

        if let Some(sol) = sol {
            let verify = cnf.verify(&sol);
            println!("verifying solution: {:?}", verify);

            if !verify {
                panic!("failed to verify solution");
            }
        }

        println!()
    }

    for i in 1..30 {
        let file = format!("data/uf20-91/uf20-0{}.cnf", i);
        let cnf = parse_file(&file).unwrap();

        let time = std::time::Instant::now();
        let clauses = cnf.clauses;

        let cnf = Cnf::from(clauses);
        let mut state: Cdcl = Solver::new(cnf);

        let sol = state.solve();

        println!("{:?}", sol);
        println!("time: {:?}", time.elapsed());

        if let Some(sol) = sol {
            let verify = state.cnf.verify(&sol);

            println!("verifying solution: {:?}", verify);

            if !verify {
                panic!("failed to verify solution");
            }
        }
    }
}

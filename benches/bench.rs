use criterion::{criterion_group, criterion_main, Criterion};
use sat_solver::sat::assignment::{HashMapAssignment, VecAssignment};
use sat_solver::sat::propagation::{PropagationQueue, PropagationStack};
use sat_solver::sat::state::Solver;
use sat_solver::sat::state::State;
use sat_solver::sudoku::solver::{Board, Sudoku, EXAMPLE_SIXTEEN};
use std::hint::black_box;

fn bench_sudoku(c: &mut Criterion) {
    let board = EXAMPLE_SIXTEEN
        .iter()
        .map(|x| x.to_vec())
        .collect::<Vec<_>>();

    let sudoku = Sudoku::new(Board::from(board));
    let cnf = sudoku.to_cnf();

    c.bench_function("sudoku - vec assignment and queue", |b| {
        b.iter(|| {
            let mut state: State<VecAssignment, PropagationQueue> = State::new(cnf.clone());
            let sol = state.solve();
            black_box(sol);
        })
    });

    c.bench_function("sudoku - vec assignment and stack", |b| {
        b.iter(|| {
            let mut state: State<VecAssignment, PropagationStack> = State::new(cnf.clone());
            let sol = state.solve();
            black_box(sol);
        })
    });

    c.bench_function("sudoku - hash map assignment and queue", |b| {
        b.iter(|| {
            let mut state: State<HashMapAssignment, PropagationQueue> = State::new(cnf.clone());
            let sol = state.solve();
            black_box(sol);
        })
    });

    c.bench_function("sudoku - hash map assignment and stack", |b| {
        b.iter(|| {
            let mut state: State<HashMapAssignment, PropagationStack> = State::new(cnf.clone());
            let sol = state.solve();
            black_box(sol);
        })
    });
}

criterion_group!(benches, bench_sudoku);

criterion_main!(benches);

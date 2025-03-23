use criterion::{criterion_group, criterion_main, Criterion};
use sat_solver::sat::assignment::{Assignment, HashMapAssignment, VecAssignment};
use sat_solver::sat::cdcl::Cdcl;
use sat_solver::sat::literal::{
    DoubleLiteral, Literal, NegativeLiteral, PackedLiteral, StructLiteral,
};
use sat_solver::sat::phase_saving::{PhaseSelector, RandomPhases, SavedPhases};
use sat_solver::sat::preprocessing::{
    PureLiteralElimination, SubsumptionElimination, TautologyElimination,
};
use sat_solver::sat::restarter::{Exponential, Geometric, Linear, Luby, Never, Restarter};
use sat_solver::sat::solver::{Solver, SolverConfig};
use sat_solver::sat::variable_selection::{FixedOrder, RandomOrder, VariableSelection, Vsids};
use sat_solver::sudoku::solver::{Board, Sudoku, EXAMPLE_SIXTEEN};
use std::fmt::{Debug, Formatter};
use std::hint::black_box;
use std::marker::PhantomData;
use std::time::Duration;
use sat_solver::sat::propagation::{Propagator, UnitSearch, WatchedLiterals};

#[derive(Debug, Clone)]
struct AssignmentConfig<A: Assignment>(PhantomData<A>);

impl<A: Assignment + Debug> SolverConfig for AssignmentConfig<A> {
    type Assignment = A;
    type VariableSelector = Vsids;
    type Literal = PackedLiteral;
    type Restarter = Luby;
    type PhaseSelector = SavedPhases;
    type Propagator = WatchedLiterals<PackedLiteral, A>;
}

#[derive(Debug, Clone)]
struct SelectorConfig<V: VariableSelection>(PhantomData<V>);

impl<V: VariableSelection + Debug> SolverConfig for SelectorConfig<V> {
    type Assignment = VecAssignment;
    type VariableSelector = V;
    type Literal = PackedLiteral;
    type Restarter = Luby;
    type PhaseSelector = SavedPhases;
    type Propagator = WatchedLiterals<PackedLiteral, VecAssignment>;
}

#[derive(Debug, Clone)]
struct RestarterConfig<R: Restarter>(PhantomData<R>);
impl<R: Restarter + Debug> SolverConfig for RestarterConfig<R> {
    type Assignment = VecAssignment;
    type VariableSelector = Vsids;
    type Literal = PackedLiteral;
    type Restarter = R;
    type PhaseSelector = SavedPhases;
    type Propagator = WatchedLiterals<PackedLiteral, VecAssignment>;
}

#[derive(Debug, Clone)]

struct LiteralConfig<L: Literal>(PhantomData<L>);
impl<L: Literal + Debug> SolverConfig for LiteralConfig<L> {
    type Assignment = VecAssignment;
    type VariableSelector = Vsids;
    type Literal = L;
    type Restarter = Luby;
    type PhaseSelector = SavedPhases;
    type Propagator = WatchedLiterals<L, VecAssignment>;
}

#[derive(Debug, Clone)]
struct PhaseSelectorConfig<P: PhaseSelector>(PhantomData<P>);

impl<P: PhaseSelector + Debug> SolverConfig for PhaseSelectorConfig<P> {
    type Assignment = VecAssignment;
    type VariableSelector = Vsids;
    type Literal = PackedLiteral;
    type Restarter = Luby;
    type PhaseSelector = P;
    type Propagator = WatchedLiterals<PackedLiteral, VecAssignment>;
}

#[derive(Debug, Clone)]
struct PropagatorConfig<Prop: Propagator<L, A>, L: Literal, A: Assignment>(PhantomData<(Prop, L, A)>);

impl<Prop: Propagator<L, A> + Debug, L: Literal, A: Assignment + Debug> SolverConfig
    for PropagatorConfig<Prop, L, A>
{
    type Assignment = A;
    type VariableSelector = Vsids;
    type Literal = L;
    type Restarter = Luby;
    type PhaseSelector = SavedPhases;
    type Propagator = Prop;
}

fn bench_sudoku(c: &mut Criterion) {
    let board = EXAMPLE_SIXTEEN
        .iter()
        .map(|x| x.to_vec())
        .collect::<Vec<_>>();

    let sudoku = Sudoku::new(Board::from(board));
    let cnf = sudoku.to_cnf();

    c.bench_function("sudoku - vec assignment", |b| {
        b.iter(|| {
            let mut state: Cdcl<AssignmentConfig<VecAssignment>> = Solver::new(cnf.clone());
            let sol = state.solve();
            black_box(sol);
        })
    });

    c.bench_function("sudoku - hash map assignment", |b| {
        b.iter(|| {
            let mut state: Cdcl<AssignmentConfig<HashMapAssignment>> = Solver::new(cnf.clone());
            let sol = state.solve();
            black_box(sol);
        })
    });
}

fn solve_3sat<Config: SolverConfig>() {
    for i in 1..1000 {
        let file = format!("data/uf20-91/uf20-0{}.cnf", i);
        let cnf = sat_solver::sat::dimacs::parse_file(&file).unwrap();
        let mut state: Cdcl<Config> = Solver::new(cnf.clone());
        let sol = state.solve();
        black_box(sol);
    }
}

fn solve_graph_colouring<Config: SolverConfig>() {
    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        let cnf = sat_solver::sat::dimacs::parse_file(&file).unwrap();
        let mut state: Cdcl<Config> = Solver::new(cnf.clone());
        let sol = state.solve();
        black_box(sol);
    }
}

fn solve_graph_colouring_with_preprocessors(
    tautology_elimination: bool,
    pure_literal: bool,
    subsumption_elimination: bool,
) {
    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        let cnf = sat_solver::sat::dimacs::parse_file(&file).unwrap();

        let mut state: Cdcl = Solver::new(cnf.clone());

        if tautology_elimination {
            state.add_preprocessor(TautologyElimination);
        }
        if pure_literal {
            state.add_preprocessor(PureLiteralElimination);
        }
        if subsumption_elimination {
            state.add_preprocessor(SubsumptionElimination);
        }

        let sol = state.solve();
        black_box(sol);
    }
}

fn bench_3sat(c: &mut Criterion) {
    let mut cnfs = Vec::new();
    for i in 1..1000 {
        let file = format!("data/uf20-91/uf20-0{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    let mut group = c.benchmark_group("3sat - restarter");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    group.bench_function("Luby", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<RestarterConfig<Luby>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Geometric", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<RestarterConfig<Geometric>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Linear", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<RestarterConfig<Linear>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Exponential", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<RestarterConfig<Exponential>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Never", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<RestarterConfig<Never>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });
}

fn bench_graph_colouring(c: &mut Criterion) {
    let mut group = c.benchmark_group("graph_colouring - literal layout");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    group.bench_function("Packed", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<LiteralConfig<PackedLiteral>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    group.bench_function("Doubled", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<LiteralConfig<DoubleLiteral>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    group.bench_function("Struct", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<LiteralConfig<StructLiteral>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    group.bench_function("Negated", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<LiteralConfig<NegativeLiteral>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.finish();

    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    let mut group = c.benchmark_group("graph_colouring - restart strategy");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    group.bench_function("Luby", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<RestarterConfig<Luby>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Geometric", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<RestarterConfig<Geometric>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Linear", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<RestarterConfig<Linear>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Exponential", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<RestarterConfig<Exponential>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Never", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<RestarterConfig<Never>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.finish();

    let mut group = c.benchmark_group("graph_colouring - Variable selection");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    group.bench_function("Vsids", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<SelectorConfig<Vsids>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Fixed Order", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<SelectorConfig<FixedOrder>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Random Order", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<SelectorConfig<RandomOrder>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.finish();

    let mut group = c.benchmark_group("graph_colouring - Assignment type");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    group.bench_function("Vec", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<AssignmentConfig<VecAssignment>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Hashmap", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<AssignmentConfig<HashMapAssignment>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.finish();

    let mut group = c.benchmark_group("graph_colouring - Phase saving");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    group.bench_function("Saved Phases", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<PhaseSelectorConfig<SavedPhases>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Random Phases", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<PhaseSelectorConfig<RandomPhases>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });

    group.finish();

    let mut group = c.benchmark_group("graph_colouring - Preprocessing");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));

    let mut cnfs = Vec::new();

    for i in 1..100 {
        let file = format!("data/flat30-60/flat30-{}.cnf", i);
        match sat_solver::sat::dimacs::parse_file(&file) {
            Ok(cnf) => cnfs.push(cnf),
            Err(e) => eprintln!("Failed to parse {}: {}", file, e),
        }
    }

    let cnfs_for_preprocessors = cnfs.clone();

    group.bench_function("Tautology", |b| {
        b.iter(|| {
            for cnf in &cnfs_for_preprocessors {
                let mut state: Cdcl = Solver::new(cnf.clone());
                state.add_preprocessor(TautologyElimination);
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Pure Literal", |b| {
        b.iter(|| {
            for cnf in &cnfs_for_preprocessors {
                let mut state: Cdcl = Solver::new(cnf.clone());
                state.add_preprocessor(PureLiteralElimination);
                black_box(state.solve());
            }
        })
    });

    group.bench_function("Subsumption", |b| {
        b.iter(|| {
            for cnf in &cnfs_for_preprocessors {
                let mut state: Cdcl = Solver::new(cnf.clone());
                state.add_preprocessor(SubsumptionElimination);
                black_box(state.solve());
            }
        })
    });

    group.finish();
    
    let mut group = c.benchmark_group("graph_colouring - Propagator");
    group.sample_size(100);
    group.measurement_time(Duration::from_secs(20));
    
    group.bench_function("WatchedLiterals", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<PropagatorConfig<WatchedLiterals<PackedLiteral, VecAssignment>, PackedLiteral, VecAssignment>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });
    
    group.bench_function("Linear checking", |b| {
        b.iter(|| {
            for cnf in &cnfs {
                let mut state: Cdcl<PropagatorConfig<UnitSearch<PackedLiteral, VecAssignment>, PackedLiteral, VecAssignment>> = Solver::new(cnf.clone());
                black_box(state.solve());
            }
        })
    });
    
    group.finish();
    
}

criterion_group!(benches, bench_graph_colouring);

criterion_main!(benches);

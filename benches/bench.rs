use criterion::measurement::Measurement;
use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion, /* Throughput, */};
use itertools::Itertools;
use sat_solver::sat::assignment::{Assignment, HashMapAssignment, VecAssignment};
use sat_solver::sat::cdcl::Cdcl;
use sat_solver::sat::clause_management::{
    ClauseManagement, LbdClauseManagement, NoClauseManagement,
};
use sat_solver::sat::clause_storage::LiteralStorage;
use sat_solver::sat::cnf::Cnf;
use sat_solver::sat::dimacs;
use sat_solver::sat::dpll::Dpll;
use sat_solver::sat::literal::{
    DoubleLiteral, Literal, NegativeLiteral, PackedLiteral, StructLiteral,
};
use sat_solver::sat::preprocessing::{
    Preprocessor, PureLiteralElimination, SubsumptionElimination, TautologyElimination,
};
use sat_solver::sat::propagation::{Propagator, UnitSearch, WatchedLiterals};
use sat_solver::sat::restarter::{Fixed, Geometric, Linear, Luby, Never, Restarter};
use sat_solver::sat::solver::{solver_config, DefaultConfig, Solver, SolverConfig};
use sat_solver::sat::variable_selection::{
    FixedOrder, JeroslowWangOneSided, JeroslowWangTwoSided, VariableSelection, Vsids, VsidsHeap,
};
use smallvec::SmallVec;
use std::fmt::Debug;
use std::hint::black_box;
use std::path::Path;
use std::time::Duration;

#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

solver_config! (
    <A: Assignment>
    AssignmentConfig {
        Literal = PackedLiteral,
        LiteralStorage = SmallVec<[PackedLiteral; 8]>,
        Assignment = A,
        VariableSelector = Vsids,
        Propagator = WatchedLiterals<PackedLiteral, SmallVec<[PackedLiteral; 8]>, A>,
        Restarter = Luby<2>,
        ClauseManager = LbdClauseManagement<PackedLiteral, SmallVec<[PackedLiteral; 8]>, 10>,
    }
);

solver_config!(
    <V: VariableSelection<PackedLiteral>>
    SelectorConfig {
        Literal = PackedLiteral,
        LiteralStorage = SmallVec<[PackedLiteral; 8]>,
        Assignment = VecAssignment,
        VariableSelector = V,
        Propagator = WatchedLiterals<PackedLiteral, SmallVec<[PackedLiteral; 8]>, VecAssignment>,
        Restarter = Luby<2>,
        ClauseManager = LbdClauseManagement<PackedLiteral, SmallVec<[PackedLiteral; 8]>, 10>,
    }
);

solver_config!(
    <R: Restarter>
    RestarterConfig {
        Literal = PackedLiteral,
        LiteralStorage = SmallVec<[PackedLiteral; 8]>,
        Assignment = VecAssignment,
        VariableSelector = Vsids,
        Propagator = WatchedLiterals<PackedLiteral, SmallVec<[PackedLiteral; 8]>, VecAssignment>,
        Restarter = R,
        ClauseManager = LbdClauseManagement<PackedLiteral, SmallVec<[PackedLiteral; 8]>, 10>,
    }
);

solver_config!(
    <L: Literal>
    LiteralConfig {
        Literal = L,
        LiteralStorage = SmallVec<[L; 8]>,
        Assignment = VecAssignment,
        VariableSelector = Vsids,
        Propagator = WatchedLiterals<L, SmallVec<[L; 8]>, VecAssignment>,
        Restarter = Luby<2>,
        ClauseManager = LbdClauseManagement<L, SmallVec<[L; 8]>, 10>,
    }
);

solver_config!(
    <Prop: Propagator<PackedLiteral, SmallVec<[PackedLiteral; 8]>, VecAssignment>>
    PropagatorConfig {
        Literal = PackedLiteral,
        LiteralStorage = SmallVec<[PackedLiteral; 8]>,
        Assignment = VecAssignment,
        VariableSelector = Vsids,
        Propagator = Prop,
        Restarter = Luby<2>,
        ClauseManager = LbdClauseManagement<PackedLiteral, SmallVec<[PackedLiteral; 8]>, 10>,
    }
);

solver_config!(
    <S: LiteralStorage<PackedLiteral>>
    LiteralStorageConfig {
        Literal = PackedLiteral,
        LiteralStorage = S,
        Assignment = VecAssignment,
        VariableSelector = Vsids,
        Propagator = WatchedLiterals<PackedLiteral, S, VecAssignment>,
        Restarter = Luby<2>,
        ClauseManager = LbdClauseManagement<PackedLiteral, S, 10>,
    }
);

solver_config! (
    <M: ClauseManagement<PackedLiteral, SmallVec<[PackedLiteral; 8]>>>
    ClauseManagerConfig {
        Literal = PackedLiteral,
        LiteralStorage = SmallVec<[PackedLiteral; 8]>,
        Assignment = VecAssignment,
        VariableSelector = Vsids,
        Propagator = WatchedLiterals<PackedLiteral, SmallVec<[PackedLiteral; 8]>, VecAssignment>,
        Restarter = Luby<2>,
        ClauseManager = M,
    }
);

fn load_cnfs(dir: &str) -> Vec<Cnf> {
    let mut cnfs = Vec::new();
    println!("Loading CNFs from {}", dir);
    let dir = Path::new(dir);
    if !dir.exists() || !dir.is_dir() {
        eprintln!("Directory {} does not exist.", dir.display());
        return cnfs;
    }
    for entry in dir.read_dir().expect("Failed to read directory") {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            let file_path = entry.path();
            if file_path.extension().and_then(|s| s.to_str()) == Some("cnf") {
                match dimacs::parse_file(file_path.to_str().expect("Invalid UTF-8")) {
                    Ok(cnf) => cnfs.push(cnf),
                    Err(_) => eprintln!("Failed to parse file"),
                }
            }
        }
    }
    println!("Loaded {} CNF files.", cnfs.len());
    if cnfs.is_empty() {
        eprintln!(
            "Warning: No CNF files were loaded. Benchmarks might not run correctly. Check the \
            path pattern: {:?}",
            dir,
        );
    }
    cnfs
}

fn run_solver_benchmark<M, S, C>(
    group: &mut BenchmarkGroup<M>,
    name: &str,
    cnfs: &[Cnf<C::Literal, C::LiteralStorage>],
) where
    M: Measurement,
    C: SolverConfig,
    S: Solver<C>,
{
    if cnfs.is_empty() {
        println!("Skipping benchmark '{}' due to no loaded CNFs.", name);
        return;
    }

    group.bench_function(name, |b| {
        b.iter(|| {
            for cnf in cnfs {
                let mut solver = S::new(cnf.clone());
                black_box(solver.solve());
            }
        })
    });
}

fn bench_solvers(c: &mut Criterion) {
    let cnfs = load_cnfs("data/flat30-60");

    {
        let mut group = c.benchmark_group("graph_colouring - Assignment type");
        group.sample_size(100);
        group.measurement_time(Duration::from_secs(20));

        run_solver_benchmark::<_, Cdcl<AssignmentConfig<VecAssignment>>, _>(
            &mut group, "Vec", &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<AssignmentConfig<HashMapAssignment>>, _>(
            &mut group, "Hashmap", &cnfs,
        );

        group.finish();
    }

    {
        let mut group = c.benchmark_group("graph_colouring - Variable selection");
        group.sample_size(100);
        group.measurement_time(Duration::from_secs(20));

        run_solver_benchmark::<_, Cdcl<SelectorConfig<VsidsHeap>>, _>(
            &mut group,
            "Vsids heap",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<SelectorConfig<Vsids>>, _>(&mut group, "Vsids", &cnfs);
        run_solver_benchmark::<_, Cdcl<SelectorConfig<JeroslowWangOneSided>>, _>(
            &mut group,
            "Jeroslow-Wang one sided",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<SelectorConfig<JeroslowWangTwoSided>>, _>(
            &mut group,
            "Jeroslow-Wang two sided",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<SelectorConfig<FixedOrder>>, _>(
            &mut group,
            "Fixed Order",
            &cnfs,
        );

        group.finish();
    }

    {
        let mut group = c.benchmark_group("graph_colouring - literal layout");
        group.sample_size(100);
        group.measurement_time(Duration::from_secs(20));

        let cnfs = cnfs.iter().map(Cnf::convert).collect_vec();
        run_solver_benchmark::<_, Cdcl<LiteralConfig<NegativeLiteral>>, _>(
            &mut group, "Negated", &cnfs,
        );
        let cnfs = cnfs.iter().map(Cnf::convert).collect_vec();
        run_solver_benchmark::<_, Cdcl<LiteralConfig<DoubleLiteral>>, _>(
            &mut group, "Doubled", &cnfs,
        );
        let cnfs = cnfs.iter().map(Cnf::convert).collect_vec();
        run_solver_benchmark::<_, Cdcl<LiteralConfig<PackedLiteral>>, _>(
            &mut group, "Packed", &cnfs,
        );
        let cnfs = cnfs.iter().map(Cnf::convert).collect_vec();
        run_solver_benchmark::<_, Cdcl<LiteralConfig<StructLiteral>>, _>(
            &mut group, "Struct", &cnfs,
        );

        group.finish();
    }

    {
        let mut group = c.benchmark_group("graph_colouring - restart strategy");
        group.sample_size(100);
        group.measurement_time(Duration::from_secs(20));

        run_solver_benchmark::<_, Cdcl<RestarterConfig<Luby<1>>>, _>(
            &mut group,
            "Luby (1x)",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<RestarterConfig<Luby<2>>>, _>(
            &mut group,
            "Luby (2x)",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<RestarterConfig<Luby<5>>>, _>(
            &mut group,
            "Luby (5x)",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<RestarterConfig<Luby<10>>>, _>(
            &mut group,
            "Luby (10x)",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<RestarterConfig<Fixed<100>>>, _>(
            &mut group,
            "Fixed (every 100)",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<RestarterConfig<Geometric<2>>>, _>(
            &mut group,
            "Geometric (x2)",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<RestarterConfig<Geometric<4>>>, _>(
            &mut group,
            "Geometric (x4)",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<RestarterConfig<Linear<100>>>, _>(
            &mut group,
            "Linear (n restarts x 100)",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<RestarterConfig<Never>>, _>(&mut group, "Never", &cnfs);

        group.finish();
    }

    {
        let mut group = c.benchmark_group("graph_colouring - Preprocessing");
        group.sample_size(100);
        group.measurement_time(Duration::from_secs(20));

        type BaseSolver = Cdcl<DefaultConfig>;

        group.bench_function("Tautology Removal", |b| {
            b.iter(|| {
                for cnf_orig in &cnfs {
                    let clauses = TautologyElimination.preprocess(cnf_orig.clauses.as_ref());
                    let cnf_processed = Cnf::from(clauses);
                    let mut state = BaseSolver::new(cnf_processed);
                    black_box(state.solve());
                }
            })
        });

        group.bench_function("Pure Literal Elimination", |b| {
            b.iter(|| {
                for cnf_orig in &cnfs {
                    let clauses = PureLiteralElimination.preprocess(cnf_orig.clauses.as_ref());
                    let cnf_processed = Cnf::from(clauses);
                    let mut state = BaseSolver::new(cnf_processed);
                    black_box(state.solve());
                }
            })
        });

        group.bench_function("Subsumption", |b| {
            b.iter(|| {
                for cnf_orig in &cnfs {
                    let clauses = SubsumptionElimination.preprocess(cnf_orig.clauses.as_ref());
                    let cnf_processed = Cnf::from(clauses);
                    let mut state = BaseSolver::new(cnf_processed);
                    black_box(state.solve());
                }
            })
        });

        run_solver_benchmark::<_, BaseSolver, _>(&mut group, "No Preprocessing", &cnfs);

        group.finish();
    }

    {
        let mut group = c.benchmark_group("graph_colouring - Propagator");
        group.sample_size(100);
        group.measurement_time(Duration::from_secs(20));

        type WatchedPropConfig = PropagatorConfig<
            WatchedLiterals<PackedLiteral, SmallVec<[PackedLiteral; 8]>, VecAssignment>,
        >;
        type UnitSearchPropConfig = PropagatorConfig<
            UnitSearch<PackedLiteral, SmallVec<[PackedLiteral; 8]>, VecAssignment>,
        >;

        run_solver_benchmark::<_, Cdcl<WatchedPropConfig>, _>(&mut group, "WatchedLiterals", &cnfs);
        run_solver_benchmark::<_, Cdcl<UnitSearchPropConfig>, _>(
            &mut group,
            "Linear checking",
            &cnfs,
        );

        group.finish();
    }

    {
        let mut group = c.benchmark_group("graph_colouring - Literal Storage");
        group.sample_size(100);
        group.measurement_time(Duration::from_secs(20));

        type SmallVec8StorageConfig = LiteralStorageConfig<SmallVec<[PackedLiteral; 8]>>;
        type SmallVec16StorageConfig = LiteralStorageConfig<SmallVec<[PackedLiteral; 16]>>;
        type VecStorageConfig = LiteralStorageConfig<Vec<PackedLiteral>>;

        let cnfs = cnfs.iter().map(Cnf::convert).collect_vec();
        run_solver_benchmark::<_, Cdcl<SmallVec8StorageConfig>, _>(
            &mut group,
            "SmallVec (8)",
            &cnfs,
        );
        let cnfs = cnfs.iter().map(Cnf::convert).collect_vec();
        run_solver_benchmark::<_, Cdcl<SmallVec16StorageConfig>, _>(
            &mut group,
            "SmallVec (16)",
            &cnfs,
        );
        let cnfs = cnfs.iter().map(Cnf::convert).collect_vec();
        run_solver_benchmark::<_, Cdcl<VecStorageConfig>, _>(&mut group, "Vec", &cnfs);

        group.finish();
    }

    {
        let mut group = c.benchmark_group("graph_colouring - CDCL vs DPLL");
        group.sample_size(100);
        group.measurement_time(Duration::from_secs(20));

        run_solver_benchmark::<_, Cdcl, _>(&mut group, "CDCL", &cnfs);
        run_solver_benchmark::<_, Dpll, _>(&mut group, "DPLL", &cnfs);

        group.finish();
    }

    {
        let mut group = c.benchmark_group("graph_colouring - Clause Management");
        group.sample_size(100);
        group.measurement_time(Duration::from_secs(20));

        type Lbd10ClauseManagerConfig = ClauseManagerConfig<
            LbdClauseManagement<PackedLiteral, SmallVec<[PackedLiteral; 8]>, 10>,
        >;
        type Lbd25ClauseManagerConfig = ClauseManagerConfig<
            LbdClauseManagement<PackedLiteral, SmallVec<[PackedLiteral; 8]>, 25>,
        >;
        type NoMgmtClauseManagerConfig =
            ClauseManagerConfig<NoClauseManagement<PackedLiteral, SmallVec<[PackedLiteral; 8]>>>;

        run_solver_benchmark::<_, Cdcl<Lbd10ClauseManagerConfig>, _>(
            &mut group,
            "LBD (check every 10)",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<Lbd25ClauseManagerConfig>, _>(
            &mut group,
            "LBD (check every 25)",
            &cnfs,
        );
        run_solver_benchmark::<_, Cdcl<NoMgmtClauseManagerConfig>, _>(&mut group, "None", &cnfs);

        group.finish();
    }
}

criterion_group!(benches, bench_solvers);
criterion_main!(benches);

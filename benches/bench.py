import sys
import time
from typing import Callable
import statistics
from pathlib import Path
import subprocess


def run_minisat(path: Path):
    subprocess.run(
        ["minisat", str(path)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
    )


def run_sat_solver(path: Path, *, is_dpll: bool = False) -> None:
    args = ["sat_solver", "file", "--path", str(path)]
    if is_dpll:
        args += ["--solver", "dpll"]

    subprocess.run(
        args,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )


def run_glucose_solver(path: Path):
    subprocess.run(
        ["../../glucose/build/glucose-simp", str(path)],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )


def benchmark_solver(solver_name: str, run_fn: Callable[[Path], None], files: list[Path]):
    print(f"\nBenchmarking {solver_name} on {min(100, len(files))} files...")

    times = []

    for i in range(100):
        if i % 10 == 0:
            print(f"Iteration {i}...")
        start = time.perf_counter()
        for file_path in files[:100]:
            run_fn(file_path)
        elapsed = time.perf_counter() - start
        times.append(elapsed)

    avg = sum(times) / len(times)
    best = min(times)
    worst = max(times)
    stddev = statistics.stdev(times)

    print(f"\nResults for {solver_name}:")
    print(f"  Best-case:    {best:.6f} s")
    print(f"  Worst-case:   {worst:.6f} s")
    print(f"  Average:      {avg:.6f} s")
    print(f"  Std Dev:      {stddev:.6f} s")


def handle_directory(directory_path: Path) -> None:
    assert directory_path.is_dir()
    files = sorted([f for f in directory_path.iterdir() if f.is_file()])
    if not files:
        print("Directory contains no files.")
        return

    # benchmark_solver(
    # "SAT Solver DPLL", lambda p: run_sat_solver(p, is_dpll=True), files
    # )
    benchmark_solver("SAT Solver", run_sat_solver, files)
    benchmark_solver("Glucose", run_glucose_solver, files)
    benchmark_solver("MiniSAT", run_minisat, files)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python bench.py <directory_path>")
        sys.exit(1)

    directory = Path(sys.argv[1])
    if not directory.exists():
        print(f"Path {directory} does not exist.")
        sys.exit(1)

    if not directory.is_dir():
        print(f"Path {directory} is not a directory.")
        sys.exit(1)

    handle_directory(directory)
    sys.exit(1)

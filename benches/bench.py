import os
import sys
import time
from pathlib import Path

def run_minisat(path: Path):
    os.system(f"minisat {path} > /dev/null 2>&1")

def run_sat_solver(path: Path):
    os.system(f"sat_solver file --path {path} > /dev/null 2>&1")

def handle_directory(directory_path: Path):
    assert directory_path.is_dir()
    assert all(file.is_file() for file in directory_path.iterdir())

    times = []

    for i in range(100):
#         if i % 10 == 0:
#             print(f"Running MiniSAT on {directory_path} iteration {i}")
        t = time.time()
        for file_path in directory_path.iterdir():
            run_minisat(file_path)

        t = time.time() - t
        times.append(t)

    avg_time = sum(times) / len(times)
    avg_time = avg_time * 1e9
    worst_case = max(times)
    worst_case = worst_case * 1e9
    best_case = min(times)
    best_case = best_case * 1e9
    print(f"Worst case time taken (MiniSAT): {worst_case} ns")
    print(f"Best case time taken (MiniSAT): {best_case} ns")
    print(f"Standard deviation (MiniSAT): {sum((x - avg_time) ** 2 for x in times) / len(times)} ns")
    print(f"Average time taken (MiniSAT): {avg_time} ns")

    times = []

    for i in range(100):
#         if i % 10 == 0:
#             print(f"Running SAT Solver on {directory_path} iteration {i}")
        t = time.time()
        for file_path in directory_path.iterdir():
            run_sat_solver(file_path)
        t = time.time() - t
        times.append(t)

    avg_time = sum(times) / len(times)
    avg_time = avg_time * 1e9
    worst_case = max(times)
    worst_case = worst_case * 1e9
    best_case = min(times)
    best_case = best_case * 1e9

    print(f"Worst case time taken (SAT Solver): {worst_case} ns")
    print(f"Best case time taken (SAT Solver): {best_case} ns")
    print(f"Standard deviation (SAT Solver): {sum((x - avg_time) ** 2 for x in times) / len(times)} ns")
    print(f"Average time taken (SAT Solver): {avg_time} ns")

def handle_file(file_path: Path):
    assert file_path.is_file()
    
    t = time.time()
    
    for i in range(100):
        if i % 10 == 0:
            print(f"Running MiniSAT on {file_path} iteration {i}")
        run_minisat(file_path)
        
    t = time.time() - t
    print(f"Average time taken (MiniSAT): {t / 100} seconds")
    
    t = time.time()
    
    for i in range(100):
        if i % 10 == 0:
            print(f"Running SAT Solver on {file_path} iteration {i}")
        run_sat_solver(file_path)
        
    t = time.time() - t
    print(f"Average time taken (SAT Solver): {t / 100} seconds")
    

if __name__ == "__main__":
    args = sys.argv[1:]
    if len(args) != 1:
        print("Usage: python bench.py <path>")
        sys.exit(1)
        
    path = args[0]
    
    path = Path(path)
    if not path.exists():
        print(f"Path {path} does not exist.")
        sys.exit(1)
    
    if path.is_dir():
        handle_directory(path)
    
    elif path.is_file():
        handle_file(path)
    else:
        print(f"Path {path} is neither a file nor a directory.")
        sys.exit(1)
    
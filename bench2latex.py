import os
import json

# Path to Criterion benchmark results
CRITERION_DIR = "target/criterion/"


def extract_benchmark_data():
    group_benchmarks = {}

    # Iterate over benchmark group directories (e.g., "graph_colouring - Assignment type")
    for group in os.listdir(CRITERION_DIR):
        group_path = os.path.join(CRITERION_DIR, group)
        if not os.path.isdir(group_path):
            continue  # Skip files, process directories only

        benchmarks = []

        # Iterate over individual benchmarks in the group (e.g., "Hashmap", "Vec")
        for benchmark in os.listdir(group_path):
            bench_path = os.path.join(group_path, benchmark, "base", "estimates.json")

            if os.path.exists(bench_path):
                with open(bench_path, "r") as f:
                    data = json.load(f)

                # Extract mean execution time and standard deviation
                mean = data.get("mean", {}).get("point_estimate", None)
                std_dev = data.get("std_dev", {}).get("point_estimate", None)

                if mean and std_dev:
                    benchmarks.append((benchmark, mean, std_dev))

        if benchmarks:
            group_benchmarks[group] = benchmarks

    return group_benchmarks


def generate_latex_tables(group_benchmarks):
    latex_sections = []

    for group, benchmarks in group_benchmarks.items():
        latex = [
            r"\begin{table}[h]",
            r"    \centering",
            rf"    \caption{{Benchmark Results for {group}}}",
            r"    \begin{tabular}{|l|c|c|}",
            r"        \hline",
            r"        Benchmark & Mean (ns) & Std Dev (ns) \\",
            r"        \hline",
        ]

        for name, mean, std_dev in benchmarks:
            latex.append(f"        {name} & {mean:.2f} & {std_dev:.2f} \\\\")

        latex.append(r"        \hline")
        latex.append(r"    \end{tabular}")
        latex.append(r"\end{table}")
        latex.append("\n")  # Add a newline between tables

        latex_sections.append("\n".join(latex))

    return "\n".join(latex_sections)


if __name__ == "__main__":
    group_benchmarks = extract_benchmark_data()

    if group_benchmarks:
        latex_tables = generate_latex_tables(group_benchmarks)

        # Save to a LaTeX file
        with open("benchmark_results.tex", "w") as f:
            f.write(latex_tables)

        print("LaTeX tables saved to benchmark_results.tex")
    else:
        print("No benchmark results found.")

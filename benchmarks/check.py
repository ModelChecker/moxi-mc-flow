import csv
import pathlib
import itertools
import sys

fnames = ["solver", "filename", "result", "tot_time"]


def get_results(filename: str) -> dict:
    results = {}
    with open(filename, "r") as f:
        reader = csv.DictReader(f, fieldnames=fnames, delimiter="\t")

        for row in reader:
            result = row["result"]
            if row["result"] == "sat" or row["result"] == "unsat":
                time = row["tot_time"]
            else:
                time = 3600

            results[row["filename"]] = (result, time)

    return results


files = [str(f) for f in pathlib.Path(sys.argv[1]).glob("*.csv")] + [
    str(f) for f in pathlib.Path(sys.argv[2]).glob("*.csv")
]

for f1, f2 in list(itertools.combinations(files, 2)):
    print(f"Comparing {f1} {f2}")

    f1_results = get_results(f1)
    f2_results = get_results(f2)

    discrepancies = []
    for filename in f1_results.keys():
        if filename not in f2_results:
            print(f"{filename} not in {f2}, but in {f1}")
            continue

        f1_res, _ = f1_results[filename]
        f2_res, _ = f2_results[filename]

        if (
            f1_res != f2_res
            and f1_res != "timeout"
            and f2_res != "timeout"
            and f1_res != "memout"
            and f2_res != "memout"
            and f1_res != "unknown"
            and f2_res != "unknown"
            and f1_res != "crash"
            and f2_res != "crash"
        ):
            discrepancies.append(filename + "," + f1 + "," + f2)

if len(discrepancies) == 0:
    print("No discrepencies")
else:
    print("Discrepencies:")
    print("\n".join(discrepancies))

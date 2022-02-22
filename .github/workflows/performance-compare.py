#!/usr/bin/env python3

from collections import defaultdict

import csv
import sys


def compare(results):
    differences = []

    for bm in results:
        if not results[bm].get("base"):
            print("Missing base result for " + bm)
            differences.append(bm)
            continue
        if not results[bm].get("pr"):
            print("Missing pr result for " + bm)
            differences.append(bm)
            continue

        b = results[bm]["base"]
        p = results[bm]["pr"]

        if b["Result"] != p["Result"]:
            print("Verification results differ for " + bm)
            differences.append(bm)
            continue

        ut_base = float(b["usertime"])
        ut_pr = float(p["usertime"])
        ut_diff = ut_pr - ut_base
        if abs(ut_diff) > 1.5:
            change = "improvement" if ut_diff < 0 else "regression"
            ut_rel = ut_diff / ut_base * 100.0
            print("Usertime {} for {}: {}s ({}%)".format(
                  change, bm, round(ut_diff, 2), round(ut_rel, 2)))
            differences.append(bm)

        mem_base = int(b["maxmem"][:-2])
        mem_pr = int(p["maxmem"][:-2])
        mem_diff = (mem_pr - mem_base) / 1024.0
        if abs(mem_diff) > 5.0:
            change = "improvement" if mem_diff < 0 else "regression"
            mem_rel = mem_diff / mem_base * 100.0
            print("Maxmem {} for {}: {}MB ({}%)".format(
                  change, bm, round(mem_diff, 2), round(mem_rel, 2)))
            differences.append(bm)

    return differences


def main():
    base = sys.argv[1]
    pr = sys.argv[2]

    results = defaultdict(defaultdict)

    with open(base) as base_file, open(pr) as pr_file:
        base_reader = csv.DictReader(base_file)
        pr_reader = csv.DictReader(pr_file)

        for b in base_reader:
            results[b["Benchmark"]]["base"] = b
        for p in pr_reader:
            results[p["Benchmark"]]["pr"] = p

    differences = compare(results)

    for d in differences:
        print("base: " + str(results[d]["base"]))
        print("pr: " + str(results[d]["pr"]))

    return 1 if len(differences) else 0


if __name__ == "__main__":
    rc = main()
    sys.exit(rc)

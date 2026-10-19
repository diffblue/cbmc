#!/usr/bin/env python3
"""Check and run regression/solver-bugs."""

import argparse
import json
import os
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                    "regression", "solver-bugs")
TEST_PL = os.path.abspath(os.path.join(ROOT, "..", "test.pl"))
CBMC = os.path.abspath(os.path.join(ROOT, "..", "..", "src", "cbmc", "cbmc"))


class Descriptor:
    def __init__(self, path):
        self.path = os.path.relpath(path, ROOT)
        with open(path) as f:
            lines = [line.rstrip("\n") for line in f
                     if not line.startswith("//")]
        lines += [""] * (3 - len(lines))
        words = lines[0].split() or [""]
        self.level, self.tags = words[0], words[1:]
        self.program, self.options = lines[1], lines[2].strip()
        self.version = (self.tags[0][len("cvc5-"):]
                        if len(self.tags) == 1
                        and self.tags[0].startswith("cvc5-")
                        and self.tags[0] != "cvc5-" else None)


def load():
    bugs = {}
    for bug in sorted(os.listdir(ROOT)):
        directory = os.path.join(ROOT, bug)
        if os.path.isdir(directory):
            bugs[bug] = [Descriptor(os.path.join(directory, name))
                         for name in sorted(os.listdir(directory))
                         if name.endswith("desc")]
    return bugs


def witness(descs):
    return next(desc for desc in descs if desc.tags == ["witness"])


def by_version(descs):
    return {desc.version: desc for desc in descs
            if desc.version is not None}


def check(bug, descs):
    witnesses = [desc for desc in descs if desc.tags == ["witness"]]
    if len(witnesses) != 1:
        return [f"{bug}: needs one descriptor tagged witness"]
    sat = witnesses[0]
    versioned = [desc for desc in descs if desc is not sat]
    errors = []
    if not versioned:
        errors.append(f"{bug}: needs at least one cvc5-<version> descriptor")
    for desc in descs:
        if desc.level != "CORE":
            errors.append(f"{desc.path}: level must be CORE")
        if desc.options:
            errors.append(f"{desc.path}: must have no options")
        if desc is not sat and desc.version is None:
            errors.append(f"{desc.path}: needs one cvc5-<version> tag")
        if desc.program != sat.program:
            errors.append(
                f"{desc.path}: must test {sat.program}, like {sat.path}")
    versions = [desc.version for desc in versioned
                if desc.version is not None]
    if len(versions) != len(set(versions)):
        errors.append(f"{bug}: has duplicate cvc5 version tags")
    return errors


def matrix(bugs, ci_cvc5):
    errors = [error for bug, descs in bugs.items()
              for error in check(bug, descs)]
    if not bugs:
        errors.append(f"{ROOT}: no tests")
    if errors:
        sys.exit("\n".join(errors))
    versions = {version for descs in bugs.values()
                for version in by_version(descs)}
    print(json.dumps({"version": sorted(versions | {ci_cvc5})}))


def test_pl(command, select, directories):
    return subprocess.run(
        [TEST_PL, "-e", "-p", "-c", command] + select + directories,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True)


def run(bugs, cbmc, cvc5, ci_cvc5):
    if cvc5 is None:
        result = test_pl(cbmc, ["-I", "witness"], list(bugs))
        print(result.stdout)
        sys.exit(result.returncode != 0)
    errors = []
    for bug, descs in bugs.items():
        desc = by_version(descs).get(cvc5)
        if desc is None:
            if cvc5 != ci_cvc5:
                continue
            desc = witness(descs)
        result = test_pl(f"{cbmc} --cvc5", ["-I", desc.tags[0]], [bug])
        if result.returncode != 0:
            errors.append(f"{desc.path}: cvc5 {cvc5} did not match\n"
                          + result.stdout)
        else:
            print(f"{bug}: {desc.path}")
    if errors:
        sys.exit("\n".join(errors))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    plan = commands.add_parser(
        "matrix", help="check the tests and print the cvc5 versions to run")
    plan.add_argument("--ci-cvc5", required=True, metavar="VERSION",
                      help="the cvc5 version CI uses (env cvc5-version)")
    test = commands.add_parser(
        "run", help="run the witness or one descriptor per cvc5 version")
    test.add_argument("--cbmc", default=CBMC)
    test.add_argument("--cvc5", metavar="VERSION",
                      help="the version of the cvc5 on PATH")
    test.add_argument("--ci-cvc5", metavar="VERSION",
                      help="the cvc5 version CI uses (env cvc5-version)")
    args = parser.parse_args()
    bugs = load()
    if args.command == "matrix":
        matrix(bugs, args.ci_cvc5)
    else:
        if args.cvc5 is not None and args.ci_cvc5 is None:
            parser.error("run with --cvc5 requires --ci-cvc5")
        run(bugs, os.path.abspath(args.cbmc), args.cvc5, args.ci_cvc5)


if __name__ == "__main__":
    main()

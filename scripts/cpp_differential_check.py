#!/usr/bin/env python3
"""Differential check of the C++ front end against g++ and clang++.

For every C++ source given (files, or every main.cpp / *.cpp below a
directory) the script

  1. compiles and runs it with each available reference compiler (g++,
     clang++), linking a harness whose `__CPROVER_assert` records the
     outcome of every assertion instead of aborting, and notes whether the
     compiler accepted the program at all;
  2. runs cbmc on it and parses the per-assertion verdicts, the
     "static_assert condition could not be evaluated" warnings and
     "static assertion failed" errors;
  3. compares the two.

Discrepancies reported (each is a class of front-end defect):

  WRONG-FAIL   an assertion that holds at run time under every reference
               compiler, but cbmc reports FAILURE (a spurious counterexample:
               something in the model is wrong -- an initializer, a
               constant, an overload choice)
  UNSOUND      an assertion that fails at run time, but cbmc reports SUCCESS
  SA-GAP       a static_assert the compilers accept but cbmc could not
               evaluate (constant evaluation gap)
  SA-WRONG     a static_assert the compilers accept but cbmc reports failed
  REJECTED     cbmc rejects (conversion/parse error) a program the compilers
               accept
  ACCEPTED     cbmc accepts a program every compiler rejects (only with
               --check-ill-formed; such inputs are otherwise skipped)

Assertions are matched by their message text, so give each `__CPROVER_assert`
a distinct message.  Assertions cbmc cannot see at run time (e.g. in a
function it never reaches) are reported only if `--strict` is given.

Typical use, as a gate over a directory of snippets:

  scripts/cpp_differential_check.py --cbmc build/bin/cbmc \\
      --std c++17 regression/cbmc-cpp/cpp17_*/main.cpp

  scripts/cpp_differential_check.py --cbmc build/bin/cbmc snippets/ \\
      --cbmc-flags="--unwind 5 --no-unwinding-assertions"

Exit status is 0 when no discrepancy was found, 1 otherwise (2 on a usage
error).  With --json the full per-file record is written for later diffing.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Dict, List, Optional, Tuple

HARNESS = r"""
#include <cstdio>
#include <cstdlib>
extern "C" void __CPROVER_assert(bool c, const char *m)
{
  std::printf("CBMC_DIFF_ASSERT %s: %s\n", c ? "PASS" : "FAIL", m);
}
extern "C" void __CPROVER_assume(bool c)
{
  if(!c)
  {
    std::printf("CBMC_DIFF_ASSUME_VIOLATED\n");
    std::fflush(stdout);
    std::_Exit(0);
  }
}
"""

# cbmc output
RE_CBMC_ASSERT = re.compile(
    r"^\[[^\]]*\.assertion\.\d+\] line \d+ (.*?): (SUCCESS|FAILURE|UNKNOWN)\s*$")
RE_CBMC_SA_GAP = re.compile(
    r"static_assert condition could not be evaluated")
RE_CBMC_SA_FAIL = re.compile(r"static assertion failed(?:: (.*))?$")
RE_CBMC_ERROR = re.compile(r"^(PARSING|CONVERSION|CBMC|TYPECHECKING) ERROR$")
# harness output
RE_RUN_ASSERT = re.compile(r"^CBMC_DIFF_ASSERT (PASS|FAIL): (.*)$")

STD_FLAG = {
    "c++98": "--cpp98", "c++03": "--cpp03", "c++11": "--cpp11",
    "c++14": "--cpp14", "c++17": "--cpp17", "c++20": "--cpp20",
    "c++23": "--cpp23", "c++26": "--cpp26",
}


def which(name: str) -> Optional[str]:
    return shutil.which(name)


def run(cmd: List[str], timeout: int, cwd: Optional[str] = None,
        memory_kb: Optional[int] = None) -> Tuple[int, str]:
    """Run a command with a wall-clock and (Linux) address-space bound."""
    def limit():
        if memory_kb:
            import resource
            resource.setrlimit(
                resource.RLIMIT_AS, (memory_kb * 1024, memory_kb * 1024))
    try:
        proc = subprocess.run(
            cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=timeout, preexec_fn=limit if memory_kb else None)
        return proc.returncode, proc.stdout.decode("utf-8", "replace")
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode("utf-8", "replace") if e.stdout else ""
        return -1, out + "\n<TIMEOUT>\n"


def guess_std(path: str, default: str) -> str:
    """cppNN_... test directories name their standard; use it."""
    m = re.search(r"cpp(98|03|11|14|17|20|23|26)", os.path.basename(
        os.path.dirname(os.path.abspath(path))) + os.path.basename(path))
    return "c++" + m.group(1) if m else default


def desc_flags(path: str) -> Optional[List[str]]:
    """The cbmc flags of a regression test.desc next to the source, if any."""
    desc = os.path.join(os.path.dirname(os.path.abspath(path)), "test.desc")
    if not os.path.exists(desc):
        return None
    lines = open(desc).read().splitlines()
    if len(lines) < 3 or os.path.basename(path) not in lines[1]:
        return None
    return lines[2].split()


def compile_and_run(compiler: str, std: str, source: str, workdir: str,
                    timeout: int, include_dirs: List[str]) -> Dict:
    """Compile source + harness with the reference compiler and run it."""
    exe = os.path.join(workdir, "a.out")
    harness = os.path.join(workdir, "harness.cpp")
    with open(harness, "w") as f:
        f.write(HARNESS)
    cmd = [compiler, "-std=" + std, "-w", "-o", exe, source, harness]
    for d in include_dirs:
        cmd += ["-I", d]
    rc, out = run(cmd, timeout, memory_kb=4 * 1024 * 1024)
    result = {"compiler": compiler, "accepted": rc == 0, "compile_output": out,
              "asserts": {}, "ran": False}
    if rc != 0:
        return result
    rc, out = run([exe], timeout, cwd=workdir, memory_kb=4 * 1024 * 1024)
    result["ran"] = rc != -1
    for line in out.splitlines():
        m = RE_RUN_ASSERT.match(line)
        if m:
            result["asserts"][m.group(2)] = m.group(1) == "PASS"
    return result


def run_cbmc(cbmc: str, flags: List[str], source: str, timeout: int,
             memory_kb: int) -> Dict:
    rc, out = run([cbmc] + flags + [source], timeout, memory_kb=memory_kb)
    result = {"rc": rc, "output": out, "asserts": {}, "sa_gaps": [],
              "sa_failed": [], "error": None, "timeout": rc == -1}
    for line in out.splitlines():
        line = re.sub(r"\x1b\[[0-9;]*m", "", line)
        m = RE_CBMC_ASSERT.match(line)
        if m:
            result["asserts"][m.group(1)] = m.group(2)
            continue
        if RE_CBMC_SA_GAP.search(line):
            result["sa_gaps"].append(line.strip())
            continue
        m = RE_CBMC_SA_FAIL.search(line)
        if m:
            result["sa_failed"].append(line.strip())
            continue
        if RE_CBMC_ERROR.match(line.strip()):
            result["error"] = line.strip()
    if rc not in (0, 10) and result["error"] is None and not result["timeout"]:
        result["error"] = "exit status %d" % rc
    return result


def compare(runs: List[Dict], cbmc: Dict, strict: bool,
            check_ill_formed: bool) -> List[Tuple[str, str]]:
    """Return (class, detail) discrepancies for one source."""
    findings = []
    accepted = [r for r in runs if r["accepted"]]
    if not accepted:
        if check_ill_formed and cbmc["error"] is None and not cbmc["timeout"]:
            findings.append(("ACCEPTED", "every reference compiler rejects "
                             "the program; cbmc accepts it"))
        return findings  # ill-formed (or uncompilable here): nothing to compare
    if cbmc["timeout"]:
        return [("TIMEOUT", "cbmc timed out")]
    if cbmc["error"] is not None:
        return [("REJECTED", cbmc["error"])]
    for line in cbmc["sa_gaps"]:
        findings.append(("SA-GAP", line))
    for line in cbmc["sa_failed"]:
        findings.append(("SA-WRONG", line))
    # run-time assertions: the reference verdict is the agreement of the
    # compilers that ran the program
    ran = [r for r in accepted if r["ran"]]
    names = set()
    for r in ran:
        names.update(r["asserts"].keys())
    for name in sorted(names):
        verdicts = {r["asserts"][name] for r in ran if name in r["asserts"]}
        if len(verdicts) != 1:
            findings.append(("COMPILERS-DISAGREE", name))
            continue
        holds = verdicts.pop()
        c = cbmc["asserts"].get(name)
        if c is None:
            if strict:
                findings.append(("NOT-CHECKED", name))
            continue
        if holds and c == "FAILURE":
            findings.append(("WRONG-FAIL", name))
        elif not holds and c == "SUCCESS":
            findings.append(("UNSOUND", name))
    return findings


def collect_sources(paths: List[str]) -> List[str]:
    out = []
    for p in paths:
        if os.path.isdir(p):
            for root, _, files in os.walk(p):
                for f in sorted(files):
                    if f.endswith(".cpp"):
                        out.append(os.path.join(root, f))
        else:
            out.append(p)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="+", help="C++ sources or directories")
    ap.add_argument("--cbmc", default="cbmc", help="cbmc binary")
    ap.add_argument("--std", default="c++17",
                    help="default language standard (a cppNN_ directory or "
                         "file name overrides it)")
    ap.add_argument("--cbmc-flags", default="",
                    help="extra cbmc flags (a test.desc next to the source "
                         "overrides them unless --ignore-desc)")
    ap.add_argument("--ignore-desc", action="store_true",
                    help="do not take cbmc flags from a test.desc")
    ap.add_argument("--compilers", default="g++,clang++",
                    help="comma-separated reference compilers")
    ap.add_argument("-I", dest="include_dirs", action="append", default=[])
    ap.add_argument("--timeout", type=int, default=300,
                    help="seconds per cbmc run (compilers: 60)")
    ap.add_argument("--memory-gb", type=int, default=12,
                    help="address-space limit for cbmc")
    ap.add_argument("--strict", action="store_true",
                    help="also report run-time assertions cbmc did not check")
    ap.add_argument("--check-ill-formed", action="store_true",
                    help="report programs cbmc accepts but every compiler "
                         "rejects")
    ap.add_argument("--json", help="write the full per-file record here")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    compilers = [c for c in args.compilers.split(",") if c and which(c)]
    if not compilers:
        print("no reference compiler found among: " + args.compilers,
              file=sys.stderr)
        return 2
    if not which(args.cbmc) and not os.path.exists(args.cbmc):
        print("cbmc binary not found: " + args.cbmc, file=sys.stderr)
        return 2

    sources = collect_sources(args.paths)
    records = []
    total_findings = 0
    for source in sources:
        std = guess_std(source, args.std)
        flags = None if args.ignore_desc else desc_flags(source)
        if flags is None:
            flags = [STD_FLAG.get(std, "--cpp17")] + args.cbmc_flags.split()
        with tempfile.TemporaryDirectory() as workdir:
            runs = [compile_and_run(c, std, source, workdir, 60,
                                    args.include_dirs) for c in compilers]
        cbmc_result = run_cbmc(args.cbmc, flags, source, args.timeout,
                               args.memory_gb * 1024 * 1024)
        findings = compare(runs, cbmc_result, args.strict,
                           args.check_ill_formed)
        total_findings += len(findings)
        status = "ok" if not findings else ",".join(
            sorted({f[0] for f in findings}))
        if not any(r["accepted"] for r in runs):
            status = "skipped (rejected by every compiler)"
        print("%-60s %s" % (source, status))
        for cls, detail in findings:
            print("    %-18s %s" % (cls, detail))
        if args.verbose and (findings or not any(r["accepted"] for r in runs)):
            for r in runs:
                if not r["accepted"]:
                    print("    -- %s rejected:" % r["compiler"])
                    for line in r["compile_output"].splitlines()[:8]:
                        print("       " + line)
        records.append({
            "source": source, "std": std, "cbmc_flags": flags,
            "compilers": [{k: v for k, v in r.items() if k != "compile_output"}
                          for r in runs],
            "cbmc": {k: v for k, v in cbmc_result.items() if k != "output"},
            "findings": findings,
        })

    if args.json:
        with open(args.json, "w") as f:
            json.dump(records, f, indent=1)
    print("\n%d source(s), %d discrepancy(ies)" % (len(sources), total_findings))
    return 1 if total_findings else 0


if __name__ == "__main__":
    sys.exit(main())

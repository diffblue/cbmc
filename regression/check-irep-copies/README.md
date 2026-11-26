# check-irep-copies self-test

Self-test corpus for the irep-copies checker (`scripts/check_irep_copies.cpp`),
which flags unnecessary `irept` copies that could be a `const` reference or a
`std::move`.

- `copy_patterns.cpp` — a self-contained fixture (a minimal `irept` stand-in
  hierarchy plus one function per case). It contains two POSITIVE cases that the
  checker must report and several NEGATIVE cases that it must not.
- `expected.txt` — the exact findings expected for `copy_patterns.cpp`.
- `run_self_test.sh` — builds the checker on demand (clang/LLVM 18), runs it
  over the fixture, and diffs the findings against `expected.txt`.

Run it with:

```sh
regression/check-irep-copies/run_self_test.sh
```

When you intentionally change the checker's heuristics, update
`copy_patterns.cpp` and/or `expected.txt` accordingly. The CI `check-irep-copies`
job runs this self-test before scanning the tree.

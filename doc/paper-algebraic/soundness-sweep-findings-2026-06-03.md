# Soundness sweep findings and fixes (2026-06-03)

This documents a corpus-scale soundness sweep of the `features/adder`
branch, the bugs it uncovered, their root-cause attribution via
`git bisect`, and the fixes applied. **Key result: the algebraic
pre-solver (Item 13/14) is sound — every wrong answer was attributable
to *other*, non-algebraic branch changes.**

## Method

- **Differential oracle sweep.** Ran `build/bin/smt2_solver` over the
  full bvmul sat-declared corpus (4,361 benchmarks, including the >2 MB
  files) plus a 4,000-file cross-corpus random sample (sat- and
  unsat-declared). Any `sat`/`unsat` answer contradicting the declared
  `:status` was flagged and cross-checked against z3 and cvc5.
- **Algebraic attribution.** Each flagged case was re-run with
  `DISABLE_ALGEBRAIC=1` to separate the algebraic layer from the rest of
  the branch.
- **Upstream attribution.** A baseline build at the merge-base
  (`1690ff0ebe`) was used to distinguish *branch-introduced* regressions
  from *pre-existing upstream* behaviour.
- **Minimisation.** `~/ddsmt.git` (ddSMT) minimised each failing input
  against a differential wrapper (branch-vs-oracle exit-code criterion).
- **Bisection.** `git bisect run` (building `smt2_solver` per step and
  testing the minimised reproducer) localised the first bad commit.

## Headline soundness result for the algebraic layer

- **0** wrong answers attributable to the algebraic pre-solver across the
  full bvmul sat corpus (4,361) and the 4,000-file cross-corpus sample.
  Every wrong-`unsat` reproduced identically with `DISABLE_ALGEBRAIC=1`.
- This **corrects** the earlier `ablation-audit-2026-06-01.md`
  characterisation of the `float` wrong-`unsat` as "pre-existing CBMC
  bit-blaster" issues: they reproduce with algebra off (so not the
  algebraic layer) but are **branch-introduced**, not upstream.

## Bugs found, root-caused, and fixed

| # | Symptom | Benchmarks | First-bad commit | Root cause | Fix commit |
|---|---------|-----------|------------------|-----------|-----------|
| 1 | wrong-`unsat` | `mcm/` (98/98 declared-sat), `float/` family | `d06d50c678` "Adjacent equality implications" | Unsound clause `(eq[i] ∨ eq[i+1])` added in `bv_utils::equal()` for 10–13-bit equality checks; asserts adjacent equality-bits can't both differ (false: `00` vs `11`), over-constraining → spurious unsat. Not the algebraic layer. | `8a6f7b2ef1` |
| 2 | wrong-`sat` | `uninterpreted-functions/uf1` | `d6f3c405a4` "deferred bit-blasting on by default" | In `boolbv.h::finish_eager_conversion`, deferred SSA equalities were replayed *after* `functions.finish_eager_conversion()`; UF applications occurring only in deferred assertions (`m(zero_extend(x))`) missed their congruence axioms → missing constraint → spurious sat. | `c1ceecbdd0` |
| 3 | wrong-`sat` | `basic-bv1/check-sat-assuming1` | (not bisected) | `check-sat-assuming` never flushed `deferred_assertions` (only `check-sat` did), so the entire regular assertion stack was ignored (`(assert false)(check-sat-assuming ())` → sat). | `9c937299ab` |
| 4 | crash (SIGABRT) | cbmc `Initialization6`, `havoc_slice/test_struct_{a,c,d}` | (algebraic layer) | `try_algebraic_solve` Level-3 candidate hint rebuilt symbols as `unsignedbv_typet(bw)` (ring width) instead of their real type; for a variable whose real width ≠ `bw` this poisoned `boolbv_map`, later tripping the `get_literals` width invariant. A soft, gate-retractable hint. | `7fab6c5d8f` |

Bug #4 is the only one in the algebraic layer itself, and it is a
**crash (safe abort), not unsoundness**.

## Minimal reproducers

- Wrong-`unsat` (from `mcm/06`; `regression/smt2_solver/adjacent-equality-soundness/`):
  ```
  (declare-const b (_ BitVec 1))
  (define-fun x () (_ BitVec 11) (_ bv0 11))
  (assert (= (_ bv0 11) (ite (= x (_ bv3 11)) (_ bv0 11) ((_ zero_extend 10) b))))
  (check-sat)            ; sat (b = 0); branch said unsat
  ```
- Wrong-`sat` UF (from `uf1`; `regression/smt2_solver/deferred-replay-congruence/`):
  ```
  (declare-const x (_ BitVec 1))
  (declare-fun m ((_ BitVec 32)) (_ BitVec 32))
  (assert (= (_ bv1 32) (m (_ bv0 32))))
  (assert (= (_ bv0 32) ((_ zero_extend 31) x)))
  (assert (= (_ bv0 32) (m ((_ zero_extend 31) x))))
  (check-sat)            ; unsat; branch said sat
  ```
- Wrong-`sat` check-sat-assuming (covered by `basic-bv1/check-sat-assuming1`):
  ```
  (assert false)(check-sat-assuming ())   ; unsat; branch said sat
  ```

## Verification after the fixes

With all four fixes in `build/bin/{cbmc,smt2_solver}`:

- Wrong-`unsat` family (reproducer, `mcm/06,12,45`, `float/e2_1,mul_03_3_1,f23`) → `sat` (correct, matching z3/cvc5).
- Wrong-`sat` family (`uf1_min`, `csa1_min`) → `unsat` (correct), with **no** `DISABLE_DEFER_BITBLAST` needed.
- 4 cbmc crash tests run to completion (rc=10) with the algebraic layer enabled.
- A genuine algebraic refutation (cohencu-style, bw=16) still returns `unsat`.
- Full `smt2_solver` regression suite passes (2 skipped); cbmc
  `algebraic-soundness-*`, `Initialization6`, `havoc_slice` pass.

## Still open

- The `mcm/` wrong-`unsat` was bisected; the `float/` family shares the
  same root cause (`d06d50c678`) and is fixed by the same commit, but was
  not independently bisected.
- `union/union_large_array` is a branch-introduced **performance**
  regression (times out where the baseline completes), non-algebraic; not
  addressed here.
- `variable-access-to-constant-array` returns rc=6 on **both** branch and
  baseline → pre-existing, not branch-introduced.
- A full post-fix corpus re-sweep (to reconfirm 0 wrong answers across all
  4,361 + sample with every fix in) has not been re-run end-to-end; the
  minimal reproducers and a sample of corpus cases were re-verified.

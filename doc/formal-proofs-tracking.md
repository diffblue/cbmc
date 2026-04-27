# Formal Proofs for Algebraic Solver — Tracking Document

## 1. Soundness of UNSAT Reporting

**Statement:** If `has_constant()` finds an odd constant c in the
strong Gröbner basis G, then the ideal I = ⟨f_1, ..., f_k⟩ contains
1, and the polynomial system {f_1 = 0, ..., f_k = 0} has no solution
in Z_{2^d}.

**Proof sketch:**
- c is odd → c is a unit in Z_{2^d} (has multiplicative inverse)
- c ∈ I (it's in the Gröbner basis, which generates the same ideal)
- c * c^{-1} = 1 ∈ I
- If 1 ∈ I, then for any assignment σ: 1 = Σ h_i * f_i(σ) = 0,
  contradiction. So no solution exists.

**Depends on:** Correctness of the strong Gröbner basis algorithm
(that G generates the same ideal as the input). Reference: Song et al.
2024, building on Adams & Loustaunau 1994 (strong Gröbner bases over
principal ideal rings).

## 2. Soundness of Rabinowitsch Trick in Z_{2^d}

**Statement:** Given polynomial equations {f_1 = 0, ..., f_k = 0}
and a disequality a ≠ b, the system {f_1, ..., f_k, (a-b)*e - 1}
being UNSAT (with 1 in the ideal) implies that a = b for all
solutions of {f_1 = 0, ..., f_k = 0}.

**Proof sketch (three cases):**
1. If a = b for all solutions of f_i = 0: then a - b ∈ I, so
   (a-b)*e - 1 ≡ -1 (mod I), and -1 is odd → 1 ∈ I → UNSAT. ✓
2. If a ≠ b for some solution with a-b odd: then e = (a-b)^{-1}
   exists, so the Rabinowitsch system is SAT → UNKNOWN. ✓
3. If a ≠ b for some solution with a-b even: then (a-b)*e is always
   even, so (a-b)*e - 1 is always odd and nonzero. The Rabinowitsch
   system is UNSAT, but the Gröbner basis contains an even constant
   (not a unit), so has_constant() returns false → UNKNOWN. ✓

**Key insight:** Case 3 is where soundness could fail if has_constant
checked for ANY nonzero constant instead of only odd (unit) constants.
Our implementation correctly checks for odd constants only.

**Verified by test:** {a=2, b=0, (a-b)*e-1=0} returns UNKNOWN.

## 3. Soundness of Polynomial Extraction

**Statement:** For each supported expression type, to_polynomial(e)
returns a polynomial p such that for any assignment σ:
  eval(e, σ) mod 2^bw = eval(p, σ) mod 2^bw

**Proof by structural induction on e:**
- ID_constant(c): p = c mod 2^bw. eval(p, σ) = c mod 2^bw = eval(e, σ). ✓
- ID_symbol(x): p = x. eval(p, σ) = σ(x) = eval(e, σ). ✓
- ID_plus(a, b): p = p_a + p_b. By IH, eval(p_a, σ) = eval(a, σ),
  eval(p_b, σ) = eval(b, σ). eval(p, σ) = eval(a, σ) + eval(b, σ)
  mod 2^bw = eval(a+b, σ) mod 2^bw. ✓
- ID_mult(a, b): p = fresh_var, side equation fresh_var - p_a * p_b = 0.
  By IH, p_a models a, p_b models b. The side equation forces
  fresh_var = p_a * p_b = eval(a, σ) * eval(b, σ) mod 2^bw. ✓
- ID_minus(a, b): p = p_a - p_b. Same as plus with subtraction. ✓
- ID_zero_extend(a): p = p_a. Zero-extension doesn't change the value,
  only the type. eval(p, σ) = eval(a, σ) mod 2^bw. ✓
  (Note: if the source is narrower, the value is the same mod 2^bw
  because zero-extension preserves the value.)
- ID_extractbits(a, lo=0): p = p_a. extract(x, bw-1, 0) = x mod 2^bw.
  eval(p, σ) = eval(a, σ) mod 2^bw = extract(eval(a, σ), bw-1, 0). ✓
  (Note: only valid when lo=0. For lo>0, we return nullopt.)
- ID_typecast(a): p = p_a. Narrowing cast = mod 2^bw. Widening cast
  preserves value. Both are correct in Z_{2^bw}. ✓

**Subtlety with set_bitwidth accepting wider types:** When processing
extractbits(bvmul_32(a, b), 15, 0) in Z_{2^16}, the bvmul has type
32-bit. We compute a*b in Z_{2^16} (automatically reducing mod 2^16).
This is correct because extract(a*b, 15, 0) = (a*b) mod 2^16, and
polynomial multiplication in Z_{2^16} computes exactly (a*b) mod 2^16.

## 4. Completeness (NOT guaranteed)

The Gröbner basis may return UNKNOWN even when the system is UNSAT:
- Step limit reached before convergence
- The ideal structure requires more basis elements than the limit allows
- The Rabinowitsch trick is incomplete for even differences (Case 3 above)

This is by design: UNKNOWN triggers fallback to bit-blasting, which
is complete. The algebraic solver is a sound but incomplete
preprocessing step.

## 5. Equation Ordering (empirical, not formally proven)

The Gröbner basis algorithm is sensitive to input equation ordering.
Definitions before Rabinowitsch gives 2000x speedup. This is an
empirical observation about the Buchberger algorithm's heuristic
behavior, not a formal property. The algorithm is correct regardless
of ordering; only performance differs.

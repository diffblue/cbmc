/-
Karatsuba multiplication identity for polynomials over a
commutative ring. Used as the soundness witness for the
polynomial Karatsuba implementation in
`src/solvers/algebraic/poly_ring.cpp::karatsuba_multiply`.

The implementation:
  f = f_lo + x^m * f_hi
  g = g_lo + x^m * g_hi
  P0 = f_lo * g_lo
  P2 = f_hi * g_hi
  P1 = (f_lo + f_hi) * (g_lo + g_hi) - P0 - P2
  f * g = P0 + x^m * P1 + x^{2m} * P2

Soundness: pure ring arithmetic. The identity is
  P0 + x^m * P1 + x^{2m} * P2 = f * g
in any commutative ring; the choice of "polynomial" structure
and the meaning of x^m is irrelevant to the algebraic identity.
We prove the identity in an arbitrary commutative ring R (which
covers ZMod (2^d) and the multivariate polynomial ring
MvPolynomial σ (ZMod (2^d)) we use in the C++ implementation).
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

open Function

namespace Karatsuba

variable {R : Type*} [CommRing R]

/-- Karatsuba's three-multiplication identity.

    For any commutative ring elements `f_lo, f_hi, g_lo, g_hi, xm`,
    the Karatsuba combination of three sub-products
    (`f_lo * g_lo`, `f_hi * g_hi`,
    `(f_lo + f_hi) * (g_lo + g_hi)`) reconstructs the four-product
    expansion `(f_lo + xm * f_hi) * (g_lo + xm * g_hi)`.

    Used to validate the multivariate polynomial Karatsuba
    multiplication in
    `src/solvers/algebraic/poly_ring.cpp::karatsuba_multiply`,
    where `xm` is `x_v^m` for a chosen main variable `v` and
    split point `m`. -/
theorem karatsuba_identity
    (f_lo f_hi g_lo g_hi xm : R) :
    let p0 := f_lo * g_lo
    let p2 := f_hi * g_hi
    let p1 := (f_lo + f_hi) * (g_lo + g_hi) - p0 - p2
    p0 + xm * p1 + xm * xm * p2 =
    (f_lo + xm * f_hi) * (g_lo + xm * g_hi) := by
  simp only
  ring

/-- Specialised form of `karatsuba_identity` for the
    main-variable split: when `xm` is treated as a formal symbol
    `x^m` in a polynomial ring, the identity is the standard
    Karatsuba decomposition. -/
theorem karatsuba_split_correct
    (f_lo f_hi g_lo g_hi xm : R) :
    f_lo * g_lo
      + xm * ((f_lo + f_hi) * (g_lo + g_hi)
              - f_lo * g_lo - f_hi * g_hi)
      + xm * xm * (f_hi * g_hi) =
    (f_lo + xm * f_hi) * (g_lo + xm * g_hi) := by
  ring

/-- Multivariate polynomial Karatsuba correctness, reduced to
    `karatsuba_identity` by treating `x_v^m` as the ring element
    `xm`. The C++ implementation's
    `multiply_by_var_power(_, v, m)` corresponds to scalar
    multiplication by `xm`. -/
theorem karatsuba_multiply_correct
    (f_lo f_hi g_lo g_hi xm : R) :
    let p0 := f_lo * g_lo
    let p2 := f_hi * g_hi
    let p1 := (f_lo + f_hi) * (g_lo + g_hi) - p0 - p2
    p0 + xm * p1 + xm * xm * p2 =
    (f_lo + xm * f_hi) * (g_lo + xm * g_hi) :=
  karatsuba_identity f_lo f_hi g_lo g_hi xm

end Karatsuba

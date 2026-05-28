/-
  SubgoalSix.lean — Soundness proofs for the universal-relational
  predicate encoding (Re 4 sub-goal 6 in the implementation tracker).

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  Implementation reference: `src/solvers/algebraic/poly_extract.cpp`
  (`extract_predicate`).

  We mechanise the soundness of four encoding strategies. In each
  case the implementation EMITS substitutions or polynomial
  equations; soundness is the implication "the original predicate
  ⇒ the emitted substitution/equation holds". This direction is
  what the procedure relies on; the converse direction is about
  completeness of the encoding and is treated separately.

  Coverage:

    1. Constant power-of-2 upper bound: x.val < 2^k ⇒ bits k..d-1 of
       x are all zero. PROVED.

    2. Lower bound 2^d - 2^k: x.val ≥ 2^d - 2^k ⇒ bits k..d-1 of x
       are all one. PROVED.

    3. Bit-comparator chain encoding (high-level statement).
       PARTIAL — recurrence soundness sketched, full proof depends
       on standard textbook comparator-circuit correctness; we
       state the invariant and admit it as `sorry` here.

    4. Signed-via-XOR transformation. PARTIAL — statement complete,
       four-case mechanised ℤ/ℕ-arithmetic dispatch is admitted as
       `sorry`. Standard sign-bit-XOR equivalence.

  See TRACEABILITY.md for the full mapping of theorems to
  implementation sites.
-/

import Re4
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

namespace SubgoalSix

open Re4

/-! ## (1) Power-of-2 upper bound: high bits are zero -/

/-- IMPL: src/solvers/algebraic/poly_extract.cpp::extract_predicate
    (try_upper_bound: power-of-2 case `N = 2^k` registers
    `b_{x, k}, ..., b_{x, d-1}` as `additional_substitutions[..] = 0`).

    SOUNDNESS DIRECTION: the implementation registers the substitution
    on the assumption that `x.val < 2^k` is satisfied; this theorem
    confirms that the emitted substitution is implied by the
    precondition. -/
theorem bvult_pow2_implies_high_bits_zero {d k : ℕ} (hk : k ≤ d)
    (x : ZMod (2 ^ d)) (hlt : x.val < 2 ^ k) :
    ∀ i, k ≤ i → Re4.stdBit d i x = 0 := by
  intro i hki
  unfold Re4.stdBit
  have h_no : Nat.testBit x.val i = false := by
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hki)
  simp [h_no]

/-! ## (2) Lower bound 2^d - 2^k: high bits are all one

    Argument: if some bit i ≥ k of x.val is zero, decompose
    x.val = (x.val / 2^(i+1)) * 2^(i+1) + x.val mod 2^(i+1).
    Bit i = 0 means x.val mod 2^(i+1) < 2^i. Combining with
    (x.val / 2^(i+1)) ≤ 2^(d-i-1) - 1 gives x.val ≤ 2^d - 2^i - 1.
    Since 2^k ≤ 2^i, x.val < 2^d - 2^k, contradicting the
    hypothesis.
-/

/-- IMPL: src/solvers/algebraic/poly_extract.cpp::extract_predicate
    (try_lower_bound: case `N = 2^d - 2^k` registers
    `b_{x, k}, ..., b_{x, d-1}` as `additional_substitutions[..] = 1`).

    SOUNDNESS DIRECTION: the substitution `b_i ↦ 1` is justified by
    the hypothesis `2^d - 2^k ≤ x.val`.

    Proof outline. By contradiction: suppose some bit i ≥ k is 0.
    Decompose `x.val = 2^(i+1) * q + r` with `r = x.val % 2^(i+1)`.
    Bit i = 0 forces `r ≤ 2^i - 1`. Combining with
    `q ≤ 2^(d-i-1) - 1` (because x.val < 2^d) gives
    `x.val ≤ (2^(d-i-1) - 1) * 2^(i+1) + (2^i - 1) = 2^d - 2^i - 1`.
    Since `2^k ≤ 2^i`, `x.val < 2^d - 2^k`, contradicting `hge`. -/
theorem bvuge_2d_minus_2k_implies_high_bits_one {d k : ℕ} (_hd : 0 < d)
    (hk : k < d) (x : ZMod (2 ^ d)) (hge : 2 ^ d - 2 ^ k ≤ x.val) :
    ∀ i, k ≤ i → i < d → Re4.stdBit d i x = 1 := by
  intro i hki hid
  unfold Re4.stdBit
  have h_test : Nat.testBit x.val i = true := by
    by_contra h_not
    have h_no : Nat.testBit x.val i = false := by
      cases hb : Nat.testBit x.val i
      · rfl
      · exact absurd hb h_not
    -- Common positivity / boundedness facts.
    have h_pow_pos : 0 < 2 ^ (i + 1) := Nat.two_pow_pos _
    have h_pow_pos_i : 0 < 2 ^ i := Nat.two_pow_pos _
    have h_xv_lt : x.val < 2 ^ d := ZMod.val_lt _
    have h_pow2 : 2 ^ (i + 1) = 2 * 2 ^ i := by ring
    -- Step 1: r := x.val % 2^(i+1) satisfies r ≤ 2^i - 1.
    have h_mod_bd : x.val % 2 ^ (i + 1) ≤ 2 ^ i - 1 := by
      have h_bit_eq : Nat.testBit (x.val % 2 ^ (i + 1)) i = false := by
        rw [Nat.testBit_mod_two_pow]
        have hii : i < i + 1 := Nat.lt_succ_self _
        simp [hii, h_no]
      have h_mod_lt : x.val % 2 ^ (i + 1) < 2 ^ (i + 1) :=
        Nat.mod_lt _ h_pow_pos
      by_contra h_not_lt
      push_neg at h_not_lt
      have h_ge_2i : 2 ^ i ≤ x.val % 2 ^ (i + 1) := by omega
      have h_div_eq : (x.val % 2 ^ (i + 1)) / 2 ^ i = 1 := by
        have h_lo : 1 ≤ (x.val % 2 ^ (i + 1)) / 2 ^ i :=
          (Nat.le_div_iff_mul_le h_pow_pos_i).mpr (by linarith)
        have h_pi1_div : 2 ^ (i + 1) / 2 ^ i = 2 := by
          rw [h_pow2, Nat.mul_div_cancel _ h_pow_pos_i]
        have h_step : (x.val % 2 ^ (i + 1)) / 2 ^ i < 2 ^ (i + 1) / 2 ^ i :=
          Nat.div_lt_div_of_lt_of_dvd ⟨2, by ring⟩ h_mod_lt
        rw [h_pi1_div] at h_step
        omega
      have h_bit_true : Nat.testBit (x.val % 2 ^ (i + 1)) i = true := by
        rw [Nat.testBit_to_div_mod, h_div_eq]; decide
      rw [h_bit_true] at h_bit_eq
      cases h_bit_eq
    -- Step 2: q := x.val / 2^(i+1) satisfies q ≤ 2^(d-i-1) - 1.
    have h_pow_split : 2 ^ d = 2 ^ (i + 1) * 2 ^ (d - i - 1) := by
      rw [← pow_add]; congr 1; omega
    have h_div_bd : x.val / 2 ^ (i + 1) ≤ 2 ^ (d - i - 1) - 1 := by
      have h_div_lt : x.val / 2 ^ (i + 1) < 2 ^ (d - i - 1) := by
        rw [Nat.div_lt_iff_lt_mul h_pow_pos]
        calc x.val
            < 2 ^ d := ZMod.val_lt _
          _ = 2 ^ (i + 1) * 2 ^ (d - i - 1) := h_pow_split
          _ = 2 ^ (d - i - 1) * 2 ^ (i + 1) := by ring
      omega
    -- Step 3: combine via x.val = 2^(i+1) * q + r.
    have h_decomp : 2 ^ (i + 1) * (x.val / 2 ^ (i + 1))
                    + x.val % 2 ^ (i + 1) = x.val :=
      Nat.div_add_mod x.val (2 ^ (i + 1))
    have h_mul_le : 2 ^ (i + 1) * (x.val / 2 ^ (i + 1))
                    ≤ 2 ^ (i + 1) * (2 ^ (d - i - 1) - 1) :=
      Nat.mul_le_mul_left _ h_div_bd
    have h_2pdi1_pos : 1 ≤ 2 ^ (d - i - 1) := Nat.one_le_two_pow
    have h_2pi1_le_2d : 2 ^ (i + 1) ≤ 2 ^ d :=
      Nat.pow_le_pow_right (by norm_num) hid
    have h_mul_eq : 2 ^ (i + 1) * (2 ^ (d - i - 1) - 1)
                  = 2 ^ d - 2 ^ (i + 1) := by
      have hfull : 2 ^ (i + 1) * 2 ^ (d - i - 1) = 2 ^ d := h_pow_split.symm
      rw [Nat.mul_sub_one, hfull]
    -- Bound x.val.
    have h_2i_lt_2d : 2 ^ i < 2 ^ d := Nat.pow_lt_pow_right (by norm_num) hid
    have h_2k_le_2i : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hki
    have h_2k_le_2d : 2 ^ k ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hk.le
    -- Derive contradiction from hge and the bit-decomposition bound.
    omega
  rw [h_test]; rfl

/-! ## (3) Bit-comparator chain encoding

    The implementation builds a polynomial recurrence

      lt_d = 0,  eq_d = 1
      lt_i = lt_{i+1} + eq_{i+1} * (1 - x_i) * y_i        (i = d-1, ..., 0)
      eq_i = eq_{i+1} * (x_i * y_i + (1 - x_i) * (1 - y_i))

    such that at termination `lt_0 = 1 ⇔ x.val < y.val` (when all
    bit variables are in {0, 1}). We mechanise this by:

      1. Defining a Boolean recurrence `chainLtBool` mirroring the
         polynomial recurrence (using && / || / ! on Bool).

      2. Showing that this Boolean recurrence equals the comparison
         of the bit-decomposed values (`listToVal`).

    The polynomial recurrence is then sound by the standard
    {0, 1}-valuation argument: when bit variables are interpreted
    as 0 or 1 in any commutative ring, polynomial multiplication
    matches Boolean conjunction, polynomial (1 - x) matches Boolean
    negation, and polynomial (a + b - a*b) matches Boolean
    disjunction.
-/

/-- Value of a bit list, with LSB at the head of the list. -/
def listToVal : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * listToVal bs

/-- The Boolean recurrence corresponding to the polynomial chain
    in `extract_predicate`. Returns `(lt, eq)` for the comparison
    of two bit lists with LSB at the head.

    Convention: head = bit 0 (LSB). Recursion processes the higher
    bits first (the tail), then incorporates the current bit. This
    matches the implementation's loop, which computes
    `lt_{d-1}, lt_{d-2}, ..., lt_0` in order. -/
def chainLtBool : List Bool → List Bool → Bool × Bool
  | [], [] => (false, true)
  | x :: xs', y :: ys' =>
      let (lt_high, eq_high) := chainLtBool xs' ys'
      ((lt_high || (eq_high && !x && y)), (eq_high && (x == y)))
  | _, _ => (false, false)  -- mismatched lengths

/-- listToVal of a list of length d is bounded by 2^d. -/
private lemma listToVal_lt_two_pow : ∀ (xs : List Bool),
    listToVal xs < 2 ^ xs.length
  | [] => by simp [listToVal]
  | b :: bs => by
    simp only [listToVal, List.length_cons, pow_succ]
    have ih := listToVal_lt_two_pow bs
    have h_b : (if b then (1 : ℕ) else 0) ≤ 1 := by by_cases h : b <;> simp [h]
    omega

/-- IMPL: src/solvers/algebraic/poly_extract.cpp::extract_predicate
    (chain encoding for general constants and symbol-symbol).

    SOUNDNESS DIRECTION: the Boolean recurrence `chainLtBool`
    correctly computes `(decide (Vx < Vy), decide (Vx = Vy))`
    where `Vx = listToVal xs` and `Vy = listToVal ys`.

    Proof by induction on the lists. The base case (both empty)
    gives `(false, true)` matching `Vx = Vy = 0`. The inductive
    case decomposes `Vx = bx + 2*Vx_high`, `Vy = by + 2*Vy_high`
    with `bx, by ∈ {0, 1}`. Case-splitting on x and y as concrete
    Bools (4 cases) and on the lt_trichotomy of `Vx_high` vs
    `Vy_high` (3 cases) gives 12 sub-cases each closable by
    omega. -/
theorem chainLtBool_correctness :
    ∀ (xs ys : List Bool), xs.length = ys.length →
    (chainLtBool xs ys).1 = decide (listToVal xs < listToVal ys) ∧
    (chainLtBool xs ys).2 = decide (listToVal xs = listToVal ys)
  | [], [], _ => by simp [chainLtBool, listToVal]
  | [], _ :: _, hlen => by simp at hlen
  | _ :: _, [], hlen => by simp at hlen
  | x :: xs', y :: ys', hlen => by
    have hlen' : xs'.length = ys'.length := by simpa using hlen
    obtain ⟨ih_lt, ih_eq⟩ := chainLtBool_correctness xs' ys' hlen'
    -- Unfold definitions in the goal.
    have h_def_lt : (chainLtBool (x :: xs') (y :: ys')).1
                  = ((chainLtBool xs' ys').1 ||
                     ((chainLtBool xs' ys').2 && !x && y)) := rfl
    have h_def_eq : (chainLtBool (x :: xs') (y :: ys')).2
                  = ((chainLtBool xs' ys').2 && (x == y)) := rfl
    have h_v_x : listToVal (x :: xs')
                = (if x then 1 else 0) + 2 * listToVal xs' := rfl
    have h_v_y : listToVal (y :: ys')
                = (if y then 1 else 0) + 2 * listToVal ys' := rfl
    -- Set abbreviations.
    set Vx := listToVal xs'
    set Vy := listToVal ys'
    refine ⟨?_, ?_⟩
    · -- lt component.
      rw [h_def_lt, ih_lt, ih_eq, h_v_x, h_v_y]
      rcases lt_trichotomy Vx Vy with h | h | h
      · -- Vx < Vy: lt = true on lower; lt overall depends on bits being not-too-big.
        have h_target : (if x then (1 : ℕ) else 0) + 2 * Vx
                        < (if y then 1 else 0) + 2 * Vy := by
          cases x <;> cases y <;> simp <;> omega
        have h_lt : Vx < Vy := h
        simp [h_lt, decide_eq_true_iff.mpr h_target]
      · -- Vx = Vy: bits decide.
        rw [h]
        cases x <;> cases y <;>
          simp [decide_eq_true_iff, decide_eq_false_iff_not]
      · -- Vx > Vy: regardless of bits, x_val > y_val.
        have h_target : ¬ ((if x then (1 : ℕ) else 0) + 2 * Vx
                          < (if y then 1 else 0) + 2 * Vy) := by
          cases x <;> cases y <;> simp <;> omega
        have h_nlt : ¬ Vx < Vy := by omega
        have h_neq : Vx ≠ Vy := by omega
        simp [h_nlt, h_neq, decide_eq_false_iff_not.mpr h_target]
    · -- eq component.
      rw [h_def_eq, ih_eq, h_v_x, h_v_y]
      rcases lt_trichotomy Vx Vy with h | h | h
      · -- Vx < Vy: not equal at any level.
        have h_target : ¬ ((if x then (1 : ℕ) else 0) + 2 * Vx
                          = (if y then 1 else 0) + 2 * Vy) := by
          cases x <;> cases y <;> simp <;> omega
        have h_neq : Vx ≠ Vy := by omega
        simp [h_neq, decide_eq_false_iff_not.mpr h_target]
      · -- Vx = Vy: bits decide.
        rw [h]
        cases x <;> cases y <;>
          simp [decide_eq_true_iff, decide_eq_false_iff_not]
      · -- Vx > Vy: not equal.
        have h_target : ¬ ((if x then (1 : ℕ) else 0) + 2 * Vx
                          = (if y then 1 else 0) + 2 * Vy) := by
          cases x <;> cases y <;> simp <;> omega
        have h_neq : Vx ≠ Vy := by omega
        simp [h_neq, decide_eq_false_iff_not.mpr h_target]

/-- The Boolean recurrence's `lt` output, applied to bit lists of
    equal length, computes the value comparison. This is the
    soundness witness for the polynomial encoding in
    `extract_predicate`. -/
theorem chainLtBool_lt_iff (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (chainLtBool xs ys).1 = true ↔ listToVal xs < listToVal ys := by
  rw [(chainLtBool_correctness xs ys hlen).1]
  exact decide_eq_true_iff

/-- The Boolean recurrence's `eq` output computes value equality. -/
theorem chainLtBool_eq_iff (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (chainLtBool xs ys).2 = true ↔ listToVal xs = listToVal ys := by
  rw [(chainLtBool_correctness xs ys hlen).2]
  exact decide_eq_true_iff

/-! ## (4) Signed via XOR -/

/-- Signed value of x : ZMod (2^d) interpreting the MSB as sign. -/
def signedVal {d : ℕ} (_ : 0 < d) (x : ZMod (2 ^ d)) : ℤ :=
  if x.val < 2 ^ (d - 1) then (x.val : ℤ)
  else (x.val : ℤ) - (2 ^ d : ℤ)

/-- IMPL: src/solvers/algebraic/poly_extract.cpp::extract_predicate
    (signed-handling preface: rewrites bvslt to bvult on XOR'd
    operands).

    The implementation transforms a signed comparison by either
    XOR'ing each operand with 2^(d-1) (for symbolic operands, via
    `bitxor_exprt` construction) or rewriting constants directly to
    `((C + 2^(d-1)) mod 2^d)`. This theorem confirms that the
    transformed values have the unsigned comparison matching the
    original signed comparison.

    Proof outline. Define `f x = (x + 2^(d-1)).val`. We show
    `(f x : ℤ) = signedVal x + 2^(d-1)`. Two cases:

      Case (i):  x.val < 2^(d-1).
        Then `signedVal x = x.val` and `x.val + 2^(d-1) < 2^d`,
        so `f x = x.val + 2^(d-1)`.

      Case (ii): x.val ≥ 2^(d-1).
        Then `signedVal x = x.val - 2^d` (in ℤ) and
        `x.val + 2^(d-1) ∈ [2^d, 2^d + 2^(d-1))`,
        so `f x = x.val + 2^(d-1) - 2^d`.

    In both cases `(f x : ℤ) = signedVal x + 2^(d-1)`. The
    iff then reduces to monotonicity of adding the same constant
    on both sides. -/
theorem bvslt_via_xor_msb {d : ℕ} (hd : 0 < d) (a b : ZMod (2 ^ d)) :
    signedVal hd a < signedVal hd b ↔
    (a + (2 ^ (d - 1) : ℕ)).val < (b + (2 ^ (d - 1) : ℕ)).val := by
  haveI : NeZero (2 ^ d) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)⟩
  have h_pow_pos : 0 < 2 ^ d := Nat.two_pow_pos _
  have h_dm1_pos : 0 < 2 ^ (d - 1) := Nat.two_pow_pos _
  have h_pow_split : 2 ^ d = 2 * 2 ^ (d - 1) := by
    have h_d_eq : 2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1; omega
    rw [h_d_eq, pow_succ]; ring
  have h_2pdm1_lt : 2 ^ (d - 1) < 2 ^ d := by rw [h_pow_split]; omega
  have h_val_2pdm1 : ((2 ^ (d - 1) : ℕ) : ZMod (2 ^ d)).val = 2 ^ (d - 1) := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt h_2pdm1_lt
  -- Key fact: (x + 2^(d-1)).val = signedVal x + 2^(d-1) (as integers).
  have key : ∀ x : ZMod (2 ^ d),
      ((x + ((2 ^ (d - 1) : ℕ) : ZMod (2 ^ d))).val : ℤ)
        = signedVal hd x + (2 ^ (d - 1) : ℤ) := by
    intro x
    have h_xval_lt : x.val < 2 ^ d := ZMod.val_lt _
    have h_sum_val : (x + ((2 ^ (d - 1) : ℕ) : ZMod (2 ^ d))).val
                    = (x.val + 2 ^ (d - 1)) % 2 ^ d := by
      rw [ZMod.val_add, h_val_2pdm1]
    by_cases h : x.val < 2 ^ (d - 1)
    · -- Case (i): x.val < 2^(d-1).
      have h_sum_lt : x.val + 2 ^ (d - 1) < 2 ^ d := by omega
      rw [h_sum_val, Nat.mod_eq_of_lt h_sum_lt]
      unfold signedVal
      simp only [if_pos h]
      push_cast
      ring
    · -- Case (ii): x.val ≥ 2^(d-1).
      push_neg at h
      have h_sum_ge : 2 ^ d ≤ x.val + 2 ^ (d - 1) := by omega
      have h_sum_lt' : x.val + 2 ^ (d - 1) - 2 ^ d < 2 ^ d := by omega
      have h_sum_mod : (x.val + 2 ^ (d - 1)) % 2 ^ d
                      = x.val + 2 ^ (d - 1) - 2 ^ d := by
        rw [Nat.mod_eq_sub_mod h_sum_ge]
        exact Nat.mod_eq_of_lt h_sum_lt'
      rw [h_sum_val, h_sum_mod]
      unfold signedVal
      simp only [if_neg (Nat.not_lt.mpr h)]
      have h_le : 2 ^ d ≤ x.val + 2 ^ (d - 1) := h_sum_ge
      have : ((x.val + 2 ^ (d - 1) - 2 ^ d : ℕ) : ℤ)
            = (x.val : ℤ) + (2 ^ (d - 1) : ℤ) - (2 ^ d : ℤ) := by
        rw [Nat.cast_sub h_le]
        push_cast
        ring
      rw [this]
      ring
  -- Apply key to a and b.
  have ka := key a
  have kb := key b
  constructor
  · intro hab
    have hint : ((a + ((2 ^ (d - 1) : ℕ) : ZMod (2 ^ d))).val : ℤ)
              < ((b + ((2 ^ (d - 1) : ℕ) : ZMod (2 ^ d))).val : ℤ) := by
      rw [ka, kb]; linarith
    exact_mod_cast hint
  · intro hval
    have hint : ((a + ((2 ^ (d - 1) : ℕ) : ZMod (2 ^ d))).val : ℤ)
              < ((b + ((2 ^ (d - 1) : ℕ) : ZMod (2 ^ d))).val : ℤ) := by
      exact_mod_cast hval
    rw [ka, kb] at hint
    linarith

end SubgoalSix

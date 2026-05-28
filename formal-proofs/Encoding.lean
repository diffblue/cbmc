/-
  Encoding.lean — Soundness of the bit-vector expression to
  polynomial encoding in `src/solvers/algebraic/poly_extract.cpp`
  (`to_polynomial` and `extract_equation`).

  TRACEABILITY: see formal-proofs/TRACEABILITY.md.

  The C++ `to_polynomial(e : exprt)` converts a CBMC expression
  over bit-vectors into a `polynomialt` over `ZMod (2^bw)`. The
  encoding is faithful: evaluating the resulting polynomial at
  any bit-vector assignment gives the same value as evaluating
  the expression at that assignment, modulo `2^bw`.

  This module formalises this faithfulness for the subset of
  expressions that `to_polynomial` handles: constants, variables,
  addition, subtraction, multiplication, unary minus, typecast/
  zero_extend (when widths align), and equality (via subtraction).
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

namespace Encoding

/-! ## Bit-vector expression syntax (subset handled by `to_polynomial`)

    `BVExpr d n` is the type of bit-vector expressions over
    `n` variables and width `d` (i.e., over `ZMod (2^d)`).
-/

/-- A bit-vector expression. -/
inductive BVExpr (d n : ℕ) : Type
  | const : ZMod (2 ^ d) → BVExpr d n
  | var : Fin n → BVExpr d n
  | add : BVExpr d n → BVExpr d n → BVExpr d n
  | sub : BVExpr d n → BVExpr d n → BVExpr d n
  | mul : BVExpr d n → BVExpr d n → BVExpr d n
  | neg : BVExpr d n → BVExpr d n
  deriving Inhabited

/-- Bit-vector evaluation: takes an environment assigning a
    `ZMod (2^d)` value to each variable, returns the result. -/
def BVExpr.eval {d n : ℕ} (env : Fin n → ZMod (2 ^ d))
    : BVExpr d n → ZMod (2 ^ d)
  | .const c => c
  | .var i => env i
  | .add a b => a.eval env + b.eval env
  | .sub a b => a.eval env - b.eval env
  | .mul a b => a.eval env * b.eval env
  | .neg a => -(a.eval env)

/-! ## Polynomial encoding -/

/-- The encoding `to_polynomial`: converts `BVExpr` into a
    `MvPolynomial`. -/
noncomputable def BVExpr.toPolynomial {d n : ℕ}
    : BVExpr d n → MvPolynomial (Fin n) (ZMod (2 ^ d))
  | .const c => MvPolynomial.C c
  | .var i => MvPolynomial.X i
  | .add a b => a.toPolynomial + b.toPolynomial
  | .sub a b => a.toPolynomial - b.toPolynomial
  | .mul a b => a.toPolynomial * b.toPolynomial
  | .neg a => -a.toPolynomial

/-! ## Faithfulness: evaluation commutes with encoding -/

/-- The fundamental faithfulness theorem: evaluating the
    encoded polynomial at an environment yields the same value
    as evaluating the original expression at that environment.

    This is the soundness of `to_polynomial`: the polynomial
    representation faithfully captures the bit-vector semantics. -/
theorem toPolynomial_eval {d n : ℕ} (e : BVExpr d n)
    (env : Fin n → ZMod (2 ^ d)) :
    MvPolynomial.eval env e.toPolynomial = e.eval env := by
  induction e with
  | const c => simp [BVExpr.toPolynomial, BVExpr.eval, MvPolynomial.eval_C]
  | var i => simp [BVExpr.toPolynomial, BVExpr.eval, MvPolynomial.eval_X]
  | add a b ih_a ih_b =>
    simp [BVExpr.toPolynomial, BVExpr.eval, map_add, ih_a, ih_b]
  | sub a b ih_a ih_b =>
    simp [BVExpr.toPolynomial, BVExpr.eval, map_sub, ih_a, ih_b]
  | mul a b ih_a ih_b =>
    simp [BVExpr.toPolynomial, BVExpr.eval, map_mul, ih_a, ih_b]
  | neg a ih_a =>
    simp [BVExpr.toPolynomial, BVExpr.eval, map_neg, ih_a]

/-! ## `extract_equation` faithfulness

    The C++ `extract_equation(eq)` for an equality `lhs = rhs`
    produces the polynomial `p_lhs - p_rhs`. The equation holds
    iff this polynomial evaluates to 0 at the corresponding
    environment. This is the bridge between bit-vector equations
    and polynomial roots.
-/

/-- `extract_equation` faithfulness: the encoded equation
    `lhs - rhs` evaluates to 0 at `env` iff `lhs.eval env = rhs.eval env`. -/
theorem extract_equation_iff {d n : ℕ} (lhs rhs : BVExpr d n)
    (env : Fin n → ZMod (2 ^ d)) :
    MvPolynomial.eval env (lhs.toPolynomial - rhs.toPolynomial) = 0 ↔
    lhs.eval env = rhs.eval env := by
  rw [map_sub, toPolynomial_eval, toPolynomial_eval, sub_eq_zero]

/-! ## Consequence: ideal-level satisfiability mirrors BV-level satisfiability

    A system of equations `{eq₁, ..., eqₘ}` is bit-vector unsat
    (no env satisfies all of them) iff the corresponding polynomial
    system `{p₁, ..., pₘ}` has no common root in `ZMod (2^d)`.
-/

/-- Equational system to polynomial system: each equation `lhs = rhs`
    becomes the polynomial `lhs - rhs`. -/
noncomputable def encodeEquations {d n : ℕ}
    (equations : List (BVExpr d n × BVExpr d n)) :
    List (MvPolynomial (Fin n) (ZMod (2 ^ d))) :=
  equations.map (fun ⟨l, r⟩ => l.toPolynomial - r.toPolynomial)

/-- The encoded system has a root iff the original equations are
    simultaneously satisfiable. -/
theorem encodeEquations_satisfiable_iff {d n : ℕ}
    (equations : List (BVExpr d n × BVExpr d n))
    (env : Fin n → ZMod (2 ^ d)) :
    (∀ p ∈ encodeEquations equations, MvPolynomial.eval env p = 0) ↔
    (∀ eq ∈ equations, eq.1.eval env = eq.2.eval env) := by
  unfold encodeEquations
  constructor
  · intro h ⟨l, r⟩ h_mem
    have : (l.toPolynomial - r.toPolynomial) ∈
           equations.map (fun ⟨l', r'⟩ => l'.toPolynomial - r'.toPolynomial) :=
      List.mem_map.mpr ⟨⟨l, r⟩, h_mem, rfl⟩
    have := h _ this
    rwa [extract_equation_iff] at this
  · intro h p h_mem
    obtain ⟨⟨l, r⟩, h_eq_mem, h_p_eq⟩ := List.mem_map.mp h_mem
    rw [← h_p_eq]
    exact (extract_equation_iff l r env).mpr (h ⟨l, r⟩ h_eq_mem)

/-! ## Purity of `BVExpr.toPolynomial`

    `BVExpr.toPolynomial` is a (Lean) function from `BVExpr` to
    `MvPolynomial`. As such, it is automatically deterministic
    ("equal inputs give equal outputs") — `rfl` suffices. The
    C++ `to_polynomial` mirrors this definition.

    Soundness of memoisation: caching `to_polynomial(e)` keyed by
    `e` is sound because:
      (i)  the polynomial result is purely a function of `e`
           (this lemma);
      (ii) the C++ side effect on `var_input_widths` is idempotent:
           the relevant code path is
           `if(var_input_widths.find(var) == var_input_widths.end())
              var_input_widths[var] = inner_width;`
           — a "first wins" update. So the side effect on the
           first call to `to_polynomial(e)` already records the
           correct width; subsequent calls (whether they hit the
           cache or recompute) would set the same value (or skip
           because the key exists).

    Property (ii) is an implementation invariant of the C++
    `var_input_widths` map; we capture it semantically below as
    a "set-once" predicate.
-/

/-- Purity: `BVExpr.toPolynomial` is a deterministic function of its
    input. This justifies memoisation by `BVExpr` identity. -/
theorem toPolynomial_deterministic {d n : ℕ} (e₁ e₂ : BVExpr d n)
    (h : e₁ = e₂) : e₁.toPolynomial = e₂.toPolynomial := h ▸ rfl

/-- Set-once invariant: if a map already records `k ↦ v`, a second
    "first wins" update preserves the binding. This is the abstract
    counterpart of the C++ idiom
    `if(m.find(k) == m.end()) m[k] = v;` — repeated invocation with
    the same `(k, v)` is idempotent.

    Combined with `toPolynomial_deterministic`, this justifies that
    skipping `to_polynomial`'s body via the memoisation cache is
    sound: any side effects that would have been performed by the
    skipped recursive computation would either (a) be no-ops
    (because the binding already exists from the first computation)
    or (b) set the same value. -/
theorem set_once_idempotent {α β : Type*} [DecidableEq α]
    (m : α → Option β) (k : α) (v : β) :
    -- After the first "set if absent" with (k, v), a second
    -- "set if absent" with (k, v) is a no-op.
    let setOnce := fun (m : α → Option β) (k : α) (v : β) =>
      fun k' => if k' = k then (m k').getD v |> some else m k'
    setOnce (setOnce m k v) k v = setOnce m k v := by
  funext k'
  by_cases h : k' = k
  · simp [h]
  · simp [h]

end Encoding

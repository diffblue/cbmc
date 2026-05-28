# Mathlib Contribution Candidates

This file records lemmas proven in this project that are general-purpose,
self-contained, and not currently in mathlib. They are candidates for
contribution back to mathlib.

## Source files
All candidates currently live in `StrongGB.lean`, mostly in the
`StrongGB.MathlibCandidates` namespace.

## Candidates

### 1. `IsLocalRing (ZMod (p^n))` for prime `p`, `n ≥ 1`

**Statement** (`StrongGB.MathlibCandidates.isLocalRing_ZMod_prime_pow`):
```lean
instance isLocalRing_ZMod_prime_pow {p : ℕ} (hp : Nat.Prime p) (n : ℕ)
    [hn : Fact (0 < n)] [NeZero (p ^ n)] :
    IsLocalRing (ZMod (p ^ n))
```

**Status**: fully proven, zero sorry, only standard axioms.

**Why it's a good candidate**: ZMod(p^n) being a local ring is a basic,
classical fact that mathlib should arguably already have. We verified it
is not currently in mathlib via `grep -rn "isLocalRing.*ZMod\|ZMod.*isLocalRing" mathlib`.

**Mathlib location suggestion**: `Mathlib/Data/ZMod/Basic.lean` or
`Mathlib/RingTheory/LocalRing/Basic.lean`.

---

### 2. `not_isUnit_iff_prime_dvd_val` in `ZMod (p^n)`

**Statement** (`StrongGB.MathlibCandidates.not_isUnit_iff_prime_dvd_val`):
```lean
private lemma not_isUnit_iff_prime_dvd_val {p n : ℕ}
    (hp : Nat.Prime p) (_hn : 0 < n) [NeZero (p ^ n)] (x : ZMod (p ^ n)) :
    ¬ IsUnit x → p ∣ x.val
```

**Status**: fully proven, zero sorry. Currently `private` but easily made
public.

**Why it's a good candidate**: Characterising non-units in a prime-power
ZMod is useful infrastructure for any work involving `ZMod (p^n)`. The
contrapositive is also natural.

**Mathlib location suggestion**: `Mathlib/Data/ZMod/Basic.lean`.

**Note**: `ZMod.isUnit_iff_coprime` exists in mathlib but doesn't directly
give the prime-power formulation.

---

### 3. `sq_eq_self_of_zmod_two_pow`: idempotents in `ZMod (2^d)` are `{0, 1}`

**Statement** (`StrongGB.sq_eq_self_of_zmod_two_pow`):
```lean
theorem sq_eq_self_of_zmod_two_pow {d : ℕ} (hd : 0 < d) (x : ZMod (2 ^ d))
    (hx : x ^ 2 = x) : x = 0 ∨ x = 1
```

**Status**: fully proven, zero sorry.

**Why it's a good candidate**: This generalises mathlib's
`eq_zero_or_one_of_sq_eq_self` — that lemma requires
`CancelMonoidWithZero` (no zero divisors), but `ZMod (2^d)` has zero
divisors for `d ≥ 2`. Despite this, idempotents in `ZMod (2^d)` still
form `{0, 1}` (a non-trivial fact that requires the prime-power structure).

A more general theorem would be: in `ZMod (p^n)` for prime `p`,
idempotents are exactly `{0, 1}`. The proof we have specialises to `p = 2`
but generalises directly.

**Mathlib location suggestion**: `Mathlib/Data/ZMod/Basic.lean`.

---

### 4. `isUnit_of_odd_nat_in_two_pow` and `isUnit_iff_two_not_dvd_val`

**Statements** (`StrongGB.MathlibCandidates`):
```lean
lemma isUnit_of_odd_nat_in_two_pow {d : ℕ} (hd : 0 < d) {n : ℕ}
    (hn : ¬ 2 ∣ n) : IsUnit (n : ZMod (2 ^ d))

lemma isUnit_iff_two_not_dvd_val {d : ℕ} (hd : 0 < d) (x : ZMod (2 ^ d)) :
    IsUnit x ↔ ¬ 2 ∣ x.val
```

**Status**: fully proven, zero sorry.

**Why they're candidates**: These specialise the general
`ZMod.isUnit_iff_coprime` to the `2^d` case in a more usable form.
Useful for anyone doing arithmetic in `ZMod (2^d)`.

**Mathlib location suggestion**: `Mathlib/Data/ZMod/Basic.lean`.

---

## Negative results (not candidates, but worth noting)

### `two_trick_saturation_complete_is_false`

This is project-specific (it depends on the `strongGB` axiom) so it's
not directly a mathlib candidate. But it's a clean, axiom-rigorous
demonstration that the natural refined statement of strong-GB completeness
(with idempotency-only hypothesis) is provably false. Useful as
documentation of why the "naive" approach doesn't work.

---

## Preparation checklist for mathlib PRs

When ready to submit:
- [ ] Extract each lemma to a standalone file (no project dependencies)
- [ ] Match mathlib naming conventions (e.g., `ZMod.sq_eq_self_iff`
      instead of our current name)
- [ ] Generalise to `ZMod (p^n)` where applicable (currently we only do
      `ZMod (2^d)` for some)
- [ ] Add `simp` and `instance` attributes appropriately
- [ ] Write proper docstrings in mathlib style
- [ ] Open mathlib PRs with descriptive titles

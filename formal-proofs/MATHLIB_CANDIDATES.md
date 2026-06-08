# Mathlib Contribution Candidates

This file records lemmas proven in this project that are general-purpose,
self-contained, and not currently in mathlib.

## Status

**PRs are prepared and ready to push.** Working clone:
`/home/ubuntu/mathlib-prs/mathlib4` with three branches off
mathlib commit `aa936c36e8`:

| Branch | PR Title | File(s) | Lines |
|--------|----------|---------|------:|
| `kiro-zmod-isunit-prime-pow` | feat(Data/ZMod/Basic): isUnit characterisation in prime power moduli | `Mathlib/Data/ZMod/Basic.lean` | +15 |
| `kiro-zmod-sq-eq-self` | feat(Data/ZMod/Basic): idempotents in ZMod (p^d) are exactly {0, 1} | `Mathlib/Data/ZMod/Basic.lean` | +56 |
| `kiro-zmod-islocalring` | feat(Data/ZMod/IsLocalRing): ZMod (p^n) is a local ring | `Mathlib/Data/ZMod/IsLocalRing.lean` (new) | +41 |

All three branches:
- Build cleanly against mathlib v4.18.0 (verified locally)
- Use only standard mathlib axioms
- Match mathlib naming conventions and proof style
- Avoid unnecessary tactic imports (no `ring`, `norm_num` —
  proofs use only what `Mathlib.Data.ZMod.Basic` already imports)

The three branches can all be merged independently:
- PR 1 and PR 2 modify the same file but at different locations
  (no conflicts).
- PR 3 creates a new file. **Depends on PR 1** for
  `ZMod.not_isUnit_iff_prime_dvd_val`.

## Contributions

### 1. `ZMod.isUnit_iff_not_prime_dvd_val` and `ZMod.not_isUnit_iff_prime_dvd_val`

**Branch**: `kiro-zmod-isunit-prime-pow`

```lean
lemma isUnit_iff_not_prime_dvd_val {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (x : ZMod (p ^ n)) : IsUnit x ↔ ¬ p ∣ x.val

lemma not_isUnit_iff_prime_dvd_val {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (x : ZMod (p ^ n)) : ¬ IsUnit x ↔ p ∣ x.val
```

Specialises `isUnit_iff_coprime` to prime power moduli, where
coprimality reduces to a simple divisibility check.

### 2. `ZMod.sq_eq_self_iff_eq_zero_or_one`

**Branch**: `kiro-zmod-sq-eq-self`

```lean
theorem sq_eq_self_iff_eq_zero_or_one {p d : ℕ} (hp : p.Prime) (hd : 0 < d)
    {x : ZMod (p ^ d)} : x ^ 2 = x ↔ x = 0 ∨ x = 1
```

Generalises `eq_zero_or_one_of_sq_eq_self` (which requires
`CancelMonoidWithZero`) to prime-power moduli, which have zero
divisors for `d ≥ 2`. Proof: lift to ℕ, use that consecutive
integers are coprime, then apply Euclid's lemma to conclude
`p^d` divides one of `x.val` or `x.val - 1`.

### 3. `ZMod.instIsLocalRingPowPrime`

**Branch**: `kiro-zmod-islocalring` (depends on PR 1)

```lean
instance instIsLocalRingPowPrime {p : ℕ} [Fact p.Prime] (n : ℕ) [Fact (0 < n)] :
    IsLocalRing (ZMod (p ^ n))
```

A clean, classical instance not currently in mathlib. The maximal
ideal is `(p)`, and a non-unit is exactly an element whose canonical
lift is divisible by `p`. Proof via `IsLocalRing.of_nonunits_add`.

## Note on the original 4 candidates

The original list had 4 candidates. The two `isUnit_iff_two_not_dvd_val`
and `isUnit_of_odd_nat_in_two_pow` (specialisations to `p = 2`) are
1-line corollaries of `ZMod.isUnit_iff_not_prime_dvd_val` (PR 1) and
do not warrant separate PRs — users can call `isUnit_iff_not_prime_dvd_val
Nat.prime_two ...` directly when needed.

## Submission steps

When ready to push and create PRs:

```bash
cd /home/ubuntu/mathlib-prs/mathlib4

# For each branch:
git checkout kiro-zmod-isunit-prime-pow
git push origin kiro-zmod-isunit-prime-pow
# Create PR via GitHub web UI or gh pr create

git checkout kiro-zmod-sq-eq-self
git push origin kiro-zmod-sq-eq-self
# (independent, can be created in parallel)

git checkout kiro-zmod-islocalring
git push origin kiro-zmod-islocalring
# Note in the PR description: depends on the isUnit-prime-pow PR
```

A `gh` token with mathlib repo access is required to push.

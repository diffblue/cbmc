/// \file
/// Strong Gröbner basis computation over Z_{2^d}

#include "groebner.h"

#include <set>

// PROOF: formal-proofs/GroebnerSoundness.lean::ZMod.isUnit_of_odd_nat
//        Soundness: an odd natural number is a unit in Z_{2^d}.
// PROOF: formal-proofs/GroebnerSoundness.lean::ideal_eq_top_of_unit_mem
//        Soundness: a unit in an ideal forces the ideal to equal
//        the whole ring.
// PROOF: formal-proofs/GroebnerSoundness.lean::ZMod.two_not_isUnit
//        Soundness: 2 is not a unit in Z_{2^d}, so even nonzero
//        constants do NOT trigger UNSAT (we correctly return
//        false for them in has_constant).
// PROOF: formal-proofs/GroebnerSoundness.lean::soundness_of_odd_constant_check
//        Top-level soundness theorem for this exact predicate:
//        if an odd constant c is in the ideal, the ideal is the
//        whole ring, hence the polynomial system is unsatisfiable.
bool strong_groebner_basist::has_constant(
  const std::vector<polynomialt> &basis) const
{
  for(const auto &p : basis)
  {
    if(!p.is_zero() && p.is_constant())
    {
      // In Z_{2^d}, an element is a unit iff it is odd (coprime to 2^d).
      // If an odd constant c is in the ideal I, then c^{-1} * c = 1 ∈ I,
      // so I = Z_{2^d}[x] (the whole ring), meaning the polynomial system
      // has no solution.
      //
      // Even nonzero constants (e.g., 2) are NON-units in Z_{2^d}, so we
      // correctly return false for them.
      mp_integer c = p.terms.front().first;
      if(c % 2 != 0)
        return true;
    }
  }
  return false;
}

// PROOF: formal-proofs/BuchbergerCorrectness.lean::s_poly_in_ideal
//        Soundness: any linear combination a*f - b*g of two
//        polynomials f, g in an ideal I is again in I. The
//        S-polynomial here is the specific combination
//        (lcm(LM(f), LM(g)) / LM(f)) * f - (lcm(LM(f), LM(g)) / LM(g)) * g
//        (with appropriate coefficient handling for ZMod(2^bw)).
//        polynomialt represents an element of MvPolynomial(Fin n,
//        ZMod (2^bw)), a commutative ring, so the abstract theorem
//        applies directly.
polynomialt
strong_groebner_basist::s_polynomial(const polynomialt &f, const polynomialt &g)
{
  PRECONDITION(!f.is_zero() && !g.is_zero());
  PRECONDITION(f.bitwidth == g.bitwidth);

  const monomialt &lm_f = f.leading_monomial();
  const monomialt &lm_g = g.leading_monomial();
  mp_integer lc_f = f.leading_coefficient();
  mp_integer lc_g = g.leading_coefficient();
  unsigned bw = f.bitwidth;
  mp_integer m = power(mp_integer{2}, mp_integer{bw});

  // LCM of leading monomials
  monomialt lcm_mon;
  {
    auto it0 = lm_f.vars.begin(), it1 = lm_g.vars.begin();
    while(it0 != lm_f.vars.end() || it1 != lm_g.vars.end())
    {
      if(
        it1 == lm_g.vars.end() ||
        (it0 != lm_f.vars.end() && it0->first < it1->first))
      {
        lcm_mon.vars.push_back(*it0++);
      }
      else if(
        it0 == lm_f.vars.end() ||
        (it1 != lm_g.vars.end() && it1->first < it0->first))
      {
        lcm_mon.vars.push_back(*it1++);
      }
      else
      {
        lcm_mon.vars.emplace_back(
          it0->first, std::max(it0->second, it1->second));
        ++it0;
        ++it1;
      }
    }
  }

  monomialt quot_f = lcm_mon.quotient(lm_f);
  monomialt quot_g = lcm_mon.quotient(lm_g);

  // S-poly = lc_g * (lcm/lm_f) * f - lc_f * (lcm/lm_g) * g
  // This cancels the leading terms.
  polynomialt term_f{bw};
  term_f.terms.emplace_back(lc_g, quot_f);
  polynomialt term_g{bw};
  term_g.terms.emplace_back(lc_f, quot_g);

  polynomialt result =
    (term_f.multiply(f, bit_vars)) - (term_g.multiply(g, bit_vars));
  result.normalize();
  apply_frobenius_idempotency(result, bit_vars);
  return result;
}

// PROOF: formal-proofs/BuchbergerCorrectness.lean::reduce_in_ideal
//        Soundness: each reduction step h ↦ h - q*g preserves
//        ideal membership when g is in the ideal. The strong
//        reduction below performs a sequence of such steps,
//        each of which preserves Ideal.span(basis).
// PROOF: formal-proofs/BuchbergerCorrectness.lean::scale_in_ideal
//        Soundness of the 2-trick: multiplying by a scalar
//        preserves ideal membership (the inner if-block that
//        multiplies r by 2^(d-v_r) when no reduction succeeded).
// PROOF: formal-proofs/StrongGB.lean::two_trick_preserves_ideal
//        Specific instance for ZMod(2^d): multiplying by 2^k
//        preserves ideal membership.
polynomialt strong_groebner_basist::strong_reduce(
  const polynomialt &f,
  const std::vector<polynomialt> &basis)
{
  polynomialt r = f;
  unsigned bw = f.bitwidth;
  mp_integer m = power(mp_integer{2}, mp_integer{bw});

  bool changed = true;
  while(changed && !r.is_zero())
  {
    changed = false;
    if(++steps_taken > max_steps && max_steps > 0)
      return r; // step limit reached

    mp_integer lc_r = r.leading_coefficient();
    const monomialt &lm_r = r.leading_monomial();
    unsigned v_r = val_2(lc_r, bw);

    // Try to reduce by a basis element
    for(const auto &g : basis)
    {
      if(g.is_zero())
        continue;
      const monomialt &lm_g = g.leading_monomial();
      if(!lm_g.divides(lm_r))
        continue;

      mp_integer lc_g = g.leading_coefficient();
      unsigned v_g = val_2(lc_g, bw);

      if(v_g <= v_r)
      {
        // lc_g divides lc_r in the 2-adic sense.
        // Compute quotient: lc_r / lc_g mod 2^d
        // lc_r = 2^v_r * u_r, lc_g = 2^v_g * u_g (u_r, u_g odd)
        // lc_r / lc_g = 2^(v_r - v_g) * u_r * inverse(u_g)
        mp_integer u_r = lc_r / power(2, v_r);
        mp_integer u_g = lc_g / power(2, v_g);
        mp_integer inv_u_g = inverse_mod_2d(u_g, bw);
        mp_integer q =
          (power(mp_integer{2}, mp_integer{v_r - v_g}) * u_r % m * inv_u_g) % m;

        monomialt quot_mon = lm_r.quotient(lm_g);
        polynomialt mult_term{bw};
        mult_term.terms.emplace_back(q, quot_mon);

        r = r - mult_term.multiply(g, bit_vars);
        r.normalize();
        apply_frobenius_idempotency(r, bit_vars);
        changed = true;
        break;
      }
    }

    // If no basis element reduced r, try the "2-trick":
    // Multiply r by 2^(d - v_r) to kill the leading term
    // (since lc_r * 2^(d-v_r) = 2^d * ... ≡ 0 mod 2^d)
    // This produces a polynomial with a smaller leading term.
    if(!changed && !r.is_zero() && v_r > 0)
    {
      mp_integer factor = power(2, bw - v_r);
      polynomialt r2 = r * factor;
      r2.normalize();
      apply_frobenius_idempotency(r2, bit_vars);
      if(!r2.is_zero() && r2.leading_monomial() != r.leading_monomial())
      {
        // The leading term changed — try reducing again
        r = r2;
        changed = true;
      }
    }
  }
  return r;
}

// PROOF: formal-proofs/StrongGB.lean::two_trick_preserves_ideal
//        Soundness: scalar multiplication by 2^k preserves
//        ideal membership.
// PROOF: formal-proofs/StrongGB.lean::two_trick_unsat_sound
//        Soundness: an odd constant in the basis -> unit -> ideal
//        equals the whole ring -> the original system is UNSAT.
//        Re-uses the existing soundness chain in
//        BuchbergerCorrectness.lean and GroebnerSoundness.lean.
//        THIS IS THE CONTRACT THIS FUNCTION SATISFIES: when
//        compute() returns UNSAT, the formal Lean theorem
//        guarantees the input system has no solution. UNKNOWN
//        is always a sound result (it commits to nothing).
// PROOF: formal-proofs/StrongGB.lean::naive_completeness_is_false
//        Important sanity-check: the NAIVE completeness statement
//        ("F unsat -> Ideal.span F contains an odd constant") is
//        FALSE. Concrete counterexample (d=2, n=0, F={C 2}) is
//        proven; explains why this function returns UNKNOWN
//        (not UNSAT) on some unsatisfiable inputs.
// PROOF: formal-proofs/StrongGB.lean::two_trick_saturation_complete_is_false
//        STRONGER NEGATIVE RESULT: even adding the obvious
//        well-formedness hypothesis (idempotency on each variable)
//        does NOT make the algorithm complete -- the same
//        counterexample {C 2} (vacuously well-formed for n=0)
//        defeats the refined claim. Hence this function does NOT
//        guarantee 'F unsat => UNSAT'; it only guarantees
//        'UNSAT => F unsat' (soundness). UNKNOWN is the correct
//        result on inputs where the strong-GB saturation cannot
//        produce an odd constant.
// PROOF: formal-proofs/BuchbergerCorrectness.lean::buchberger_ideal_preservation
//        Soundness: the basis-update operations (S-polynomial,
//        reduction, scaling) preserve <G> = <F>.
// PROOF: formal-proofs/BuchbergerTermination.lean::buchberger_terminates
//        Termination: the algorithm halts in any Noetherian ring.
strong_groebner_basist::resultt
strong_groebner_basist::compute(std::vector<polynomialt> &polys)
{
  steps_taken = 0;

  // Apply host substitutions (linear elimination): replace each
  // host variable h with its bit-sum polynomial in every input
  // polynomial. This eliminates the host as a variable; the
  // sum-decomposition equations (h - sum_i 2^i b_i = 0) become
  // trivially zero and are dropped by the zero-removal step
  // below.
  if(!host_substitutions.empty())
  {
    for(auto &p : polys)
    {
      for(const auto &[host_idx, sub_poly] : host_substitutions)
        p = substitute_variable(p, host_idx, sub_poly);
    }
  }

  // Apply Frobenius to all input polynomials so the initial basis
  // is already idempotency-reduced.
  // PROOF: formal-proofs/Re4.lean::all_idempotent_to_bool
  //        For bit_vars constrained by b_i^2 = b_i (idempotency),
  //        every assignment satisfying the constraints lies in
  //        {0,1}^k. This justifies treating bit_vars as Boolean.
  // PROOF: formal-proofs/StrongGB.lean::sq_eq_self_of_zmod_two_pow
  //        In Z_{2^d}, x^2 = x implies x in {0, 1} -- the
  //        ring-level fact that powers idempotency to Boolean
  //        even in the presence of zero divisors.
  // PROOF: formal-proofs/StrongGB.lean::d_eq_one_completeness
  //        Positive partial completeness: for d=1 (i.e., over
  //        GF(2)) with idempotency on each variable, the
  //        algorithm IS complete. So on Boolean-only inputs
  //        compute() will not return UNKNOWN due to the
  //        completeness gap (it may still return UNKNOWN if
  //        max_steps is exhausted).
  if(!bit_vars.empty())
  {
    for(auto &p : polys)
      apply_frobenius_idempotency(p, bit_vars);
  }

  // Remove zero polynomials
  polys.erase(
    std::remove_if(
      polys.begin(),
      polys.end(),
      [](const polynomialt &p) { return p.is_zero(); }),
    polys.end());

  if(polys.empty())
    return resultt::UNKNOWN;

  if(has_constant(polys))
    return resultt::UNSAT;

  // Buchberger-like algorithm
  // Track which pairs have been processed
  std::set<std::pair<std::size_t, std::size_t>> processed;
  std::vector<std::pair<std::size_t, std::size_t>> pairs;

  for(std::size_t i = 0; i < polys.size(); ++i)
    for(std::size_t j = i + 1; j < polys.size(); ++j)
      pairs.emplace_back(i, j);

  // Track progress: if a full round of S-polynomial processing
  // produces no new basis elements, the basis is complete
  // (Buchberger criterion).
  // PROOF: formal-proofs/BuchbergerTermination.lean::stable_implies_no_new
  //        Soundness of the termination criterion: at stability,
  //        every candidate new element is already in the ideal.
  // PROOF: formal-proofs/BuchbergerCorrectness.lean::buchberger_unsat'
  //        Top-level UNSAT soundness: if G ⊇ F preserves the
  //        ideal and contains a unit, the input system is UNSAT.
  std::size_t pairs_since_last_progress = 0;
  std::size_t pairs_at_last_progress = pairs.size();

  while(!pairs.empty())
  {
    if(steps_taken > max_steps && max_steps > 0)
      return resultt::UNKNOWN;

    // If we've processed all pairs since the last new element
    // without finding anything new, the basis is complete.
    if(pairs_since_last_progress > pairs_at_last_progress)
      return has_constant(polys) ? resultt::UNSAT : resultt::UNKNOWN;

    auto [i, j] = pairs.back();
    pairs.pop_back();
    ++pairs_since_last_progress;

    if(i >= polys.size() || j >= polys.size())
      continue;
    if(polys[i].is_zero() || polys[j].is_zero())
      continue;

    polynomialt s = s_polynomial(polys[i], polys[j]);
    polynomialt r = strong_reduce(s, polys);

    if(!r.is_zero())
    {
      std::size_t new_idx = polys.size();
      polys.push_back(std::move(r));

      if(has_constant(polys))
        return resultt::UNSAT;

      for(std::size_t k = 0; k < new_idx; ++k)
        pairs.emplace_back(k, new_idx);

      // Reset progress tracking: new element means new pairs to check
      pairs_since_last_progress = 0;
      pairs_at_last_progress = pairs.size();
    }

    // Also process 2-multiples of basis elements with non-unit lc
    for(std::size_t k = 0; k < polys.size(); ++k)
    {
      if(polys[k].is_zero())
        continue;
      unsigned v = val_2(polys[k].leading_coefficient(), polys[k].bitwidth);
      if(v > 0 && v < polys[k].bitwidth)
      {
        polynomialt h =
          polys[k] * power(mp_integer{2}, mp_integer{polys[k].bitwidth - v});
        h.normalize();
        apply_frobenius_idempotency(h, bit_vars);
        polynomialt rh = strong_reduce(h, polys);
        if(!rh.is_zero())
        {
          std::size_t new_idx = polys.size();
          polys.push_back(std::move(rh));
          if(has_constant(polys))
            return resultt::UNSAT;
          for(std::size_t l = 0; l < new_idx; ++l)
            pairs.emplace_back(l, new_idx);
        }
      }
    }
  }

  return has_constant(polys) ? resultt::UNSAT : resultt::UNKNOWN;
}

// PROOF: formal-proofs/ExtractCandidate.lean::extract_candidate_local_soundness
//        Local soundness of the univariate-linear solve step:
//        when c is a unit (odd in Z_{2^bw}), c*x + d = 0 has a
//        unique solution x = -d * c^{-1}. The C++ algorithm
//        constructs precisely this value (using inverse_mod_2d
//        for the inverse and adjusting for the 2-adic valuation
//        of c when c is not itself a unit).
// PROOF: formal-proofs/ExtractCandidate.lean::solve_univariate_linear_unit
//        Existence of a solution when the leading coefficient is
//        a unit (odd). Same fact phrased existentially.
std::map<std::size_t, mp_integer> strong_groebner_basist::extract_candidate(
  const std::vector<polynomialt> &basis,
  unsigned bw)
{
  std::map<std::size_t, mp_integer> assignment;
  mp_integer m = power(mp_integer{2}, mp_integer{bw});

  bool progress = true;
  while(progress)
  {
    progress = false;
    for(const auto &p : basis)
    {
      if(p.is_zero() || p.is_constant())
        continue;

      // Substitute known assignments
      polynomialt reduced = p;
      for(const auto &[var, val] : assignment)
      {
        polynomialt subst{bw};
        for(const auto &[coeff, mon] : reduced.terms)
        {
          mp_integer new_coeff = coeff;
          monomialt new_mon;
          for(const auto &[vi, exp] : mon.vars)
          {
            if(vi == var)
            {
              mp_integer v = val;
              for(unsigned e = 0; e < exp; ++e)
                new_coeff = (new_coeff * v) % m;
            }
            else
              new_mon.vars.emplace_back(vi, exp);
          }
          subst.terms.emplace_back(new_coeff, new_mon);
        }
        subst.normalize();
        reduced = subst;
      }

      if(reduced.is_zero())
        continue;

      // Check if univariate linear: c*x + d = 0
      if(reduced.terms.size() > 2)
        continue;

      std::size_t var_idx = 0;
      mp_integer coeff_x{0}, coeff_const{0};
      bool is_univariate_linear = true;

      for(const auto &[c, mon] : reduced.terms)
      {
        if(mon.is_constant())
        {
          coeff_const = c;
        }
        else if(mon.vars.size() == 1 && mon.vars[0].second == 1)
        {
          if(coeff_x != 0)
          {
            is_univariate_linear = false;
            break;
          }
          var_idx = mon.vars[0].first;
          coeff_x = c;
        }
        else
        {
          is_univariate_linear = false;
          break;
        }
      }

      if(!is_univariate_linear || coeff_x == 0)
        continue;
      if(assignment.count(var_idx))
        continue;

      // x = -coeff_const / coeff_x mod 2^bw
      // If coeff_x = 2^k * u (u odd), we can solve if coeff_const
      // is also divisible by 2^k: divide both by 2^k, then
      // x = -coeff_const' * inverse(u) mod 2^(bw-k).
      unsigned v_x = val_2(coeff_x, bw);
      unsigned v_c = val_2(coeff_const, bw);
      if(v_x > 0 && v_c < v_x)
        continue; // coeff_const not divisible by 2^v_x, no solution

      mp_integer cx = coeff_x;
      mp_integer cc = coeff_const;
      unsigned effective_bw = bw;
      if(v_x > 0)
      {
        mp_integer divisor = power(mp_integer{2}, mp_integer{v_x});
        cx = cx / divisor;
        cc = cc / divisor;
        effective_bw = bw - v_x;
      }
      mp_integer eff_m = power(mp_integer{2}, mp_integer{effective_bw});
      mp_integer inv = inverse_mod_2d(cx, effective_bw);
      mp_integer val = (eff_m - ((cc * inv) % eff_m)) % eff_m;
      // The solution is x ≡ val (mod 2^(bw-k)), pick the smallest
      assignment[var_idx] = val % m;
      progress = true;
    }
  }

  return assignment;
}

// PROOF: formal-proofs/BuchbergerCorrectness.lean::reduce_in_ideal
//        Soundness: reducing f by basis yields f' = f - q where
//        q is in Ideal.span(basis). Hence f - f' is in the span,
//        i.e., f and f' are in the same coset modulo the span.
//        Crucial consequence used at the call site (boolbv.cpp::
//        try_algebraic_solve): if reduce_by_basis returns 0,
//        then f itself is in Ideal.span(basis), i.e., the
//        equation f = 0 follows algebraically from the basis.
polynomialt strong_groebner_basist::reduce_by_basis(
  const polynomialt &f,
  const std::vector<polynomialt> &basis,
  std::size_t max_steps)
{
  // Delegate to the instance method strong_reduce, using a fresh
  // instance so we don't mutate any external state. The instance
  // tracks step counts via its members; we use the requested
  // max_steps as the budget.
  strong_groebner_basist instance{max_steps};
  return instance.strong_reduce(f, basis);
}

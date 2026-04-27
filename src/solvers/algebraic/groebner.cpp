/// \file
/// Strong Gröbner basis computation over Z_{2^d}

#include "groebner.h"

#include <set>

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
      // has no solution. This is formally verified in GroebnerSoundness.lean
      // (theorems ZMod.isUnit_of_odd_nat and ideal_eq_top_of_unit_mem).
      //
      // Even nonzero constants (e.g., 2) are NON-units in Z_{2^d}, so we
      // correctly return false for them. This is verified in
      // ZMod.two_not_isUnit (GroebnerSoundness.lean).
      mp_integer c = p.terms.front().first;
      if(c % 2 != 0)
        return true;
    }
  }
  return false;
}

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

  polynomialt result = (term_f * f) - (term_g * g);
  result.normalize();
  return result;
}

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

        r = r - (mult_term * g);
        r.normalize();
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

strong_groebner_basist::resultt
strong_groebner_basist::compute(std::vector<polynomialt> &polys)
{
  steps_taken = 0;

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
  // (Buchberger criterion — verified in BuchbergerTermination.lean,
  // theorem stable_implies_no_new).
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

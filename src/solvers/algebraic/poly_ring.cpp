/// \file
/// Polynomial ring over Z_{2^d} for algebraic bit-vector solving

#include "poly_ring.h"

#include <util/arith_tools.h>
#include <util/invariant.h>

#include <optional>

// --- monomialt ---

monomialt monomialt::operator*(const monomialt &other) const
{
  monomialt result;
  auto it0 = vars.begin(), it1 = other.vars.begin();
  while(it0 != vars.end() && it1 != other.vars.end())
  {
    if(it0->first < it1->first)
      result.vars.push_back(*it0++);
    else if(it0->first > it1->first)
      result.vars.push_back(*it1++);
    else
    {
      result.vars.emplace_back(it0->first, it0->second + it1->second);
      ++it0;
      ++it1;
    }
  }
  while(it0 != vars.end())
    result.vars.push_back(*it0++);
  while(it1 != other.vars.end())
    result.vars.push_back(*it1++);
  return result;
}

bool monomialt::divides(const monomialt &other) const
{
  auto it0 = vars.begin(), it1 = other.vars.begin();
  while(it0 != vars.end())
  {
    while(it1 != other.vars.end() && it1->first < it0->first)
      ++it1;
    if(
      it1 == other.vars.end() || it1->first != it0->first ||
      it1->second < it0->second)
      return false;
    ++it0;
    ++it1;
  }
  return true;
}

monomialt monomialt::quotient(const monomialt &divisor) const
{
  monomialt result;
  auto it0 = vars.begin(), it1 = divisor.vars.begin();
  while(it0 != vars.end())
  {
    if(it1 == divisor.vars.end() || it0->first < it1->first)
    {
      result.vars.push_back(*it0++);
    }
    else
    {
      PRECONDITION(it0->first == it1->first && it0->second >= it1->second);
      if(it0->second > it1->second)
        result.vars.emplace_back(it0->first, it0->second - it1->second);
      ++it0;
      ++it1;
    }
  }
  return result;
}

// PROOF: formal-proofs/PolyRing.lean::grevlexLt_irrefl,
//        formal-proofs/PolyRing.lean::grevlexLt_asymm,
//        formal-proofs/PolyRing.lean::grevlexLt_total
//        The graded reverse-lex order is a strict total order:
//        irreflexive, asymmetric, and total on distinct monomials.
//        These properties make this comparator well-defined for
//        std::sort and std::set, and ensure Buchberger termination.
bool monomialt::operator<(const monomialt &other) const
{
  // Graded reverse lexicographic: higher total degree is "larger" (comes first)
  unsigned d0 = total_degree(), d1 = other.total_degree();
  if(d0 != d1)
    return d0 > d1;
  // Same degree: reverse lex (last variable with different exponent decides,
  // LOWER exponent in last variable = larger)
  auto it0 = vars.rbegin(), it1 = other.vars.rbegin();
  while(it0 != vars.rend() && it1 != other.vars.rend())
  {
    if(it0->first != it1->first)
      return it0->first > it1->first;
    if(it0->second != it1->second)
      return it0->second < it1->second;
    ++it0;
    ++it1;
  }
  return vars.size() > other.vars.size();
}

bool monomialt::operator==(const monomialt &other) const
{
  return vars == other.vars;
}

// --- polynomialt ---

mp_integer polynomialt::reduce(const mp_integer &val) const
{
  mp_integer m = modulus();
  mp_integer r = val % m;
  if(r < 0)
    r += m;
  return r;
}

polynomialt::polynomialt(unsigned bw, const mp_integer &c) : bitwidth{bw}
{
  mp_integer m = power(mp_integer{2}, mp_integer{bw});
  mp_integer r = c % m;
  if(r < 0)
    r += m;
  if(r != 0)
    terms.emplace_back(r, monomialt{});
}

polynomialt::polynomialt(
  unsigned bw,
  const mp_integer &coeff,
  std::size_t var_idx)
  : bitwidth{bw}
{
  mp_integer m = power(mp_integer{2}, mp_integer{bw});
  mp_integer r = coeff % m;
  if(r < 0)
    r += m;
  if(r != 0)
    terms.emplace_back(r, monomialt{var_idx});
}

// PROOF: formal-proofs/PolyRing.lean::normalize_combine_like_terms
//        Combining terms with the same monomial preserves the
//        polynomial value (ring associativity + distributivity).
// PROOF: formal-proofs/PolyRing.lean::normalize_drop_zero_preserves_sum
//        Dropping zero-coefficient terms preserves the sum.
// Sorting by monomial order is just rearranging a sum, which
// preserves value by commutativity of addition; together these
// three operations comprise polynomialt::normalize.
void polynomialt::normalize()
{
  mp_integer m = modulus();
  // Combine like terms
  std::map<monomialt, mp_integer, std::less<monomialt>> combined;
  for(auto &[c, mon] : terms)
  {
    mp_integer &val = combined[mon];
    val = (val + c) % m;
    if(val < 0)
      val += m;
  }
  terms.clear();
  for(auto &[mon, c] : combined)
  {
    if(c != 0)
      terms.emplace_back(c, mon);
  }
  // Sort by monomial ordering (leading term first)
  std::sort(
    terms.begin(),
    terms.end(),
    [](const auto &a, const auto &b) { return a.second < b.second; });
}

polynomialt polynomialt::operator+(const polynomialt &other) const
{
  PRECONDITION(bitwidth == other.bitwidth);
  polynomialt result{bitwidth};
  result.terms.reserve(terms.size() + other.terms.size());
  result.terms.insert(result.terms.end(), terms.begin(), terms.end());
  result.terms.insert(
    result.terms.end(), other.terms.begin(), other.terms.end());
  result.normalize();
  return result;
}

polynomialt polynomialt::operator-(const polynomialt &other) const
{
  PRECONDITION(bitwidth == other.bitwidth);
  polynomialt neg = other * mp_integer{-1};
  return *this + neg;
}

polynomialt polynomialt::operator*(const mp_integer &scalar) const
{
  mp_integer m = modulus();
  mp_integer s = scalar % m;
  if(s < 0)
    s += m;
  if(s == 0)
    return polynomialt{bitwidth};
  polynomialt result{bitwidth};
  result.terms.reserve(terms.size());
  for(const auto &[c, mon] : terms)
  {
    mp_integer nc = (c * s) % m;
    if(nc < 0)
      nc += m;
    if(nc != 0)
      result.terms.emplace_back(nc, mon);
  }
  return result;
}

polynomialt polynomialt::schoolbook_multiply(const polynomialt &other) const
{
  PRECONDITION(bitwidth == other.bitwidth);
  // Streaming multiplication: accumulate term-pair products into a
  // std::map keyed by monomial as we go, instead of materialising
  // the full m*n term-pair vector and normalising afterwards.
  // Peak memory is O(unique monomials in product) instead of
  // O(m*n), which dominates SABER karatsuba2 extraction at large N.
  mp_integer m = modulus();
  std::map<monomialt, mp_integer> combined;
  for(const auto &[c0, m0] : terms)
  {
    for(const auto &[c1, m1] : other.terms)
    {
      mp_integer c = reduce(c0 * c1);
      if(c == 0)
        continue;
      monomialt mon = m0 * m1;
      mp_integer &slot = combined[mon];
      slot = (slot + c) % m;
      if(slot < 0)
        slot += m;
    }
  }
  polynomialt result{bitwidth};
  result.terms.reserve(combined.size());
  for(auto &[mon, c] : combined)
  {
    if(c != 0)
      result.terms.emplace_back(c, mon);
  }
  // combined is sorted by monomialt::operator<; copy that order.
  // No further sort required.
  return result;
}

namespace
{
/// Look up the exponent of variable `v` in monomial `m`, or 0 if
/// `v` does not occur in `m`.
unsigned exponent_of(const monomialt &m, std::size_t v)
{
  for(const auto &[var, e] : m.vars)
  {
    if(var == v)
      return e;
    if(var > v)
      break; // vars sorted by index
  }
  return 0;
}

/// Maximum exponent of variable `v` across all monomials of `f`.
unsigned max_degree_in(const polynomialt &f, std::size_t v)
{
  unsigned d = 0;
  for(const auto &[c, mon] : f.terms)
    d = std::max(d, exponent_of(mon, v));
  return d;
}

/// Pick the variable whose total degree spread (deg_f + deg_g) is
/// maximal, provided both f and g have positive degree in it.
/// Returns nullopt if no variable is shared with positive degree.
std::optional<std::size_t>
pick_main_variable(const polynomialt &f, const polynomialt &g)
{
  std::map<std::size_t, unsigned> deg_f, deg_g;
  for(const auto &[c, mon] : f.terms)
    for(const auto &[var, e] : mon.vars)
    {
      auto &slot = deg_f[var];
      slot = std::max(slot, static_cast<unsigned>(e));
    }
  for(const auto &[c, mon] : g.terms)
    for(const auto &[var, e] : mon.vars)
    {
      auto &slot = deg_g[var];
      slot = std::max(slot, static_cast<unsigned>(e));
    }
  std::optional<std::size_t> best;
  unsigned best_score = 0;
  for(const auto &[v, df] : deg_f)
  {
    auto it = deg_g.find(v);
    if(it == deg_g.end())
      continue;
    unsigned dg = it->second;
    // We need at least one half to be non-empty after splitting.
    // That requires max(df, dg) >= 2 so that m = (max+1)/2 >= 1
    // and at least some terms have exponent >= m in one of them.
    if(df + dg < 2)
      continue;
    unsigned score = df + dg;
    if(score > best_score)
    {
      best_score = score;
      best = v;
    }
  }
  return best;
}

/// Split `f` into `(f_lo, f_hi)` such that
/// `f = f_lo + x_v^m * f_hi`, where `f_lo` collects terms with
/// `v`-exponent `< m` (unchanged) and `f_hi` collects terms with
/// `v`-exponent `>= m` with the `v`-exponent reduced by `m`.
/// PROOF: trivial decomposition by case-splitting on the
///        v-exponent in each monomial; mechanised in
///        formal-proofs/Karatsuba.lean::karatsuba_split_correct.
std::pair<polynomialt, polynomialt>
split_by_var(const polynomialt &f, std::size_t v, unsigned m)
{
  polynomialt lo{f.bitwidth};
  polynomialt hi{f.bitwidth};
  lo.terms.reserve(f.terms.size());
  hi.terms.reserve(f.terms.size());
  for(const auto &[c, mon] : f.terms)
  {
    unsigned ev = exponent_of(mon, v);
    if(ev < m)
    {
      lo.terms.emplace_back(c, mon);
    }
    else
    {
      monomialt new_mon;
      new_mon.vars.reserve(mon.vars.size());
      for(const auto &[var, e] : mon.vars)
      {
        if(var == v)
        {
          unsigned new_e = e - m;
          if(new_e > 0)
            new_mon.vars.emplace_back(var, new_e);
        }
        else
        {
          new_mon.vars.emplace_back(var, e);
        }
      }
      hi.terms.emplace_back(c, new_mon);
    }
  }
  // f_lo preserves the original sort order (terms with v-exponent
  // < m can keep their relative order under grevlex). f_hi has had
  // a uniform shift on the v-exponent and may need re-sorting.
  hi.normalize();
  return {std::move(lo), std::move(hi)};
}

/// Multiply every term of `f` by `x_v^k`. Preserves coefficients
/// and the relative order of terms (a uniform shift in one
/// variable's exponent does not flip pairs under grevlex among
/// the input's monomials, but the resulting polynomial still
/// goes through normalize() to be safe and to guarantee correctness
/// regardless of the term ordering convention).
polynomialt
multiply_by_var_power(const polynomialt &f, std::size_t v, unsigned k)
{
  if(k == 0)
    return f;
  polynomialt result{f.bitwidth};
  result.terms.reserve(f.terms.size());
  for(const auto &[c, mon] : f.terms)
  {
    monomialt new_mon;
    new_mon.vars.reserve(mon.vars.size() + 1);
    bool inserted = false;
    for(const auto &[var, e] : mon.vars)
    {
      if(!inserted && var > v)
      {
        new_mon.vars.emplace_back(v, k);
        inserted = true;
      }
      if(var == v)
      {
        new_mon.vars.emplace_back(var, e + k);
        inserted = true;
      }
      else
      {
        new_mon.vars.emplace_back(var, e);
      }
    }
    if(!inserted)
      new_mon.vars.emplace_back(v, k);
    result.terms.emplace_back(c, new_mon);
  }
  result.normalize();
  return result;
}
} // namespace

/// Threshold below which Karatsuba's recursive overhead exceeds
/// the schoolbook savings. Empirically tuned via the
/// `bench-multiplication/karatsuba-microbench.cpp` benchmark on
/// dense univariate polynomials over Z_{2^32}: at term count
/// <= 64 the recursion overhead and `mp_integer` per-coefficient
/// cost dominate; at <= 128 the two methods are roughly equal;
/// above that Karatsuba pulls ahead, reaching ~2x speedup at
/// 1024 terms. We set the threshold at 96 to leave a safety
/// margin so that small cases never regress.
constexpr std::size_t KARATSUBA_THRESHOLD = 96;

polynomialt
polynomialt::karatsuba_multiply(const polynomialt &other, std::size_t v) const
{
  PRECONDITION(bitwidth == other.bitwidth);
  // PROOF: formal-proofs/Karatsuba.lean::karatsuba_identity,
  //        karatsuba_multiply_correct.
  // The Karatsuba combination
  //   P0 = f_lo * g_lo
  //   P2 = f_hi * g_hi
  //   P1 = (f_lo + f_hi) * (g_lo + g_hi) - P0 - P2
  //   result = P0 + x^m * P1 + x^{2m} * P2
  // equals (f_lo + x^m * f_hi) * (g_lo + x^m * g_hi) = f * g
  // by pure ring arithmetic, mechanised in Karatsuba.lean.
  unsigned df = max_degree_in(*this, v);
  unsigned dg = max_degree_in(other, v);
  unsigned d = std::max(df, dg);
  // m must divide both halves non-trivially.
  unsigned m = (d + 1) / 2;
  if(m == 0)
    return schoolbook_multiply(other);

  auto [f_lo, f_hi] = split_by_var(*this, v, m);
  auto [g_lo, g_hi] = split_by_var(other, v, m);

  // Karatsuba: 3 sub-multiplications.
  polynomialt p0 = f_lo * g_lo;
  polynomialt p2 = f_hi * g_hi;
  polynomialt sum_f = f_lo + f_hi;
  polynomialt sum_g = g_lo + g_hi;
  polynomialt p1 = sum_f * sum_g;
  p1 = p1 - p0 - p2;

  // Combine: f*g = P0 + x_v^m * P1 + x_v^{2m} * P2.
  polynomialt result = p0;
  result = result + multiply_by_var_power(p1, v, m);
  result = result + multiply_by_var_power(p2, v, 2 * m);
  return result;
}

polynomialt polynomialt::operator*(const polynomialt &other) const
{
  PRECONDITION(bitwidth == other.bitwidth);
  // Below the threshold, schoolbook is faster (recursion
  // overhead dominates). Above it, try to find a main variable
  // with sufficient degree spread to make Karatsuba worthwhile.
  if(
    terms.size() <= KARATSUBA_THRESHOLD ||
    other.terms.size() <= KARATSUBA_THRESHOLD)
    return schoolbook_multiply(other);
  auto v = pick_main_variable(*this, other);
  if(!v.has_value())
    return schoolbook_multiply(other);
  return karatsuba_multiply(other, *v);
}

polynomialt polynomialt::multiply(
  const polynomialt &other,
  const std::set<std::size_t> &bit_vars) const
{
  PRECONDITION(bitwidth == other.bitwidth);
  if(bit_vars.empty())
    return *this * other;

  // Streaming multiplication with inline idempotency clamping.
  mp_integer m = modulus();
  std::map<monomialt, mp_integer> combined;
  for(const auto &[c0, m0] : terms)
  {
    for(const auto &[c1, m1] : other.terms)
    {
      mp_integer c = reduce(c0 * c1);
      if(c == 0)
        continue;
      monomialt prod_m = m0 * m1;
      // Inline idempotency: clamp bit-variable exponents to 1.
      for(auto &[var, exp] : prod_m.vars)
      {
        if(exp > 1 && bit_vars.count(var) > 0)
          exp = 1;
      }
      mp_integer &slot = combined[prod_m];
      slot = (slot + c) % m;
      if(slot < 0)
        slot += m;
    }
  }
  polynomialt result{bitwidth};
  result.terms.reserve(combined.size());
  for(auto &[mon, c] : combined)
  {
    if(c != 0)
      result.terms.emplace_back(c, mon);
  }
  return result;
}

// --- Utility functions ---

// PROOF: formal-proofs/PolyRing.lean::inverse_mod_2d_correct
//        Existence and uniqueness: for odd a and d > 0, the
//        inverse mod 2^d exists and is unique. Hensel lifting is
//        one constructive way to compute it; the function below
//        implements Newton iteration (x = x*(2-a*x)) which doubles
//        2-adic precision per step.
mp_integer inverse_mod_2d(const mp_integer &a, unsigned d)
{
  PRECONDITION(a % 2 != 0); // a must be odd
  if(d == 0)
    return mp_integer{0};
  // Newton's method / Hensel lifting:
  // Start with x ≡ a (mod 2) [since a is odd, a*a ≡ 1 (mod 2)]
  mp_integer x{1};
  mp_integer m = power(mp_integer{2}, mp_integer{d});
  for(unsigned k = 1; k < d; k *= 2)
  {
    // x = x * (2 - a * x) mod 2^{min(2k, d)}
    mp_integer step_mod = power(mp_integer{2}, mp_integer{std::min(2 * k, d)});
    x = ((x * (2 - a * x)) % step_mod + step_mod) % step_mod;
  }
  return (x % m + m) % m;
}

unsigned val_2(const mp_integer &a, unsigned d)
{
  if(a == 0)
    return d;
  mp_integer v = a;
  if(v < 0)
    v = -v;
  unsigned k = 0;
  while(k < d && v % 2 == 0)
  {
    v /= 2;
    ++k;
  }
  return k;
}

// PROOF: formal-proofs/Re4.lean::frobenius_pow_eq_self
//        Soundness: in any ring, idempotent b satisfies b^k = b
//        for k >= 1, justifying the exponent-clamping below.
void apply_frobenius_idempotency(
  polynomialt &p,
  const std::set<std::size_t> &bit_vars)
{
  if(bit_vars.empty())
    return;
  bool any_change = false;
  for(auto &[coeff, mono] : p.terms)
  {
    for(auto &[var, exp] : mono.vars)
    {
      if(exp > 1 && bit_vars.count(var) > 0)
      {
        exp = 1;
        any_change = true;
      }
    }
  }
  if(any_change)
  {
    // Clamping may have produced duplicate monomials (e.g., the
    // sequence b^2 + b becomes b + b = 2b after clamping). Merge
    // duplicates and re-sort by re-normalizing.
    p.normalize();
  }
}

polynomialt
substitute_variable(const polynomialt &p, std::size_t v, const polynomialt &q)
{
  polynomialt result{p.bitwidth};
  for(const auto &[c, m] : p.terms)
  {
    // Split monomial m into m = v^k * m_rest.
    unsigned k = 0;
    monomialt m_rest;
    for(const auto &[var, exp] : m.vars)
    {
      if(var == v)
        k = exp;
      else
        m_rest.vars.emplace_back(var, exp);
    }
    if(k == 0)
    {
      // v not in m; copy term as-is.
      result.terms.emplace_back(c, m);
      continue;
    }
    // Compute c * m_rest * q^k.
    polynomialt rest_term{p.bitwidth};
    rest_term.terms.emplace_back(c, m_rest);
    polynomialt q_power{p.bitwidth, mp_integer{1}};
    for(unsigned i = 0; i < k; ++i)
      q_power = q_power * q;
    polynomialt term_result = rest_term * q_power;
    for(auto &t : term_result.terms)
      result.terms.emplace_back(std::move(t));
  }
  result.normalize();
  return result;
}

/// \file
/// Polynomial ring over Z_{2^d} for algebraic bit-vector solving

#include "poly_ring.h"

#include <util/arith_tools.h>
#include <util/invariant.h>

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

polynomialt polynomialt::operator*(const polynomialt &other) const
{
  PRECONDITION(bitwidth == other.bitwidth);
  polynomialt result{bitwidth};
  for(const auto &[c0, m0] : terms)
    for(const auto &[c1, m1] : other.terms)
      result.terms.emplace_back(reduce(c0 * c1), m0 * m1);
  result.normalize();
  return result;
}

polynomialt polynomialt::multiply(
  const polynomialt &other,
  const std::set<std::size_t> &bit_vars) const
{
  PRECONDITION(bitwidth == other.bitwidth);
  if(bit_vars.empty())
    return *this * other;

  polynomialt result{bitwidth};
  for(const auto &[c0, m0] : terms)
  {
    for(const auto &[c1, m1] : other.terms)
    {
      monomialt prod_m = m0 * m1;
      // Inline idempotency: clamp bit-variable exponents to 1 during
      // monomial construction. Avoids materialising b_i^k terms for
      // k >= 2; downstream normalize() then merges duplicate
      // monomials more aggressively.
      for(auto &[var, exp] : prod_m.vars)
      {
        if(exp > 1 && bit_vars.count(var) > 0)
          exp = 1;
      }
      result.terms.emplace_back(reduce(c0 * c1), std::move(prod_m));
    }
  }
  result.normalize();
  return result;
}

// --- Utility functions ---

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

/// \file
/// Vanishing polynomial test over Z_{2^m}

#include "vanishing.h"

#include <set>
#include <util/arith_tools.h>

#include <algorithm>

/// Compute the 2-adic valuation of n (largest k such that 2^k divides n)
static unsigned nu2(const mp_integer &n)
{
  if(n == 0)
    return 999;
  mp_integer abs_n = n < 0 ? -n : n;
  unsigned k = 0;
  while(abs_n % 2 == 0)
  {
    abs_n /= 2;
    ++k;
  }
  return k;
}

/// Compute SF(2^m): smallest k such that 2^m divides k!
static unsigned smarandache_function(unsigned m)
{
  unsigned val = 0;
  for(unsigned k = 1;; ++k)
  {
    val += nu2(mp_integer{k});
    if(val >= m)
      return k;
  }
}

/// Check if a univariate polynomial vanishes over Z_{2^m}
/// using Singmaster's theorem (falling factorial decomposition).
static bool is_vanishing_univariate(
  const std::vector<mp_integer> &coeffs,
  unsigned m)
{
  mp_integer mod = power(mp_integer{2}, mp_integer{m});

  // Reduce coefficients mod 2^m
  std::vector<mp_integer> c(coeffs.size());
  for(std::size_t i = 0; i < coeffs.size(); ++i)
  {
    c[i] = coeffs[i] % mod;
    if(c[i] < 0)
      c[i] += mod;
  }

  // Remove leading zeros
  while(c.size() > 1 && c.back() == 0)
    c.pop_back();
  if(c.size() == 1 && c[0] == 0)
    return true;

  unsigned n = smarandache_function(m);

  // Convert to falling factorial basis and check divisibility.
  // The falling factorial Y_k(x) = x(x-1)...(x-k+1) has leading
  // coefficient 1 in x^k. We iteratively extract the Y_k component
  // from highest degree down.
  //
  // For degree k: the coefficient of x^k in Y_k is 1, so the
  // coefficient c_k in the falling factorial expansion equals
  // the coefficient of x^k in the current polynomial.
  // Then subtract c_k * Y_k and continue.

  // Build falling factorial coefficients for Y_0 through Y_n
  // Y_k[j] = coefficient of x^j in Y_k(x)
  std::vector<std::vector<mp_integer>> Y(n + 1);
  Y[0] = {1};
  for(unsigned k = 1; k <= n; ++k)
  {
    Y[k].resize(k + 1, 0);
    // Y_k = (x - (k-1)) * Y_{k-1}
    for(unsigned j = 0; j < Y[k - 1].size(); ++j)
    {
      Y[k][j + 1] += Y[k - 1][j];
      Y[k][j] -= mp_integer(k - 1) * Y[k - 1][j];
    }
  }

  // Extract falling factorial coefficients from highest degree down
  int deg = (int)c.size() - 1;
  for(int k = std::min(deg, (int)n); k >= 0; --k)
  {
    if(k > deg || (k < (int)c.size() && c[k] == 0))
      continue;

    mp_integer ck = (k < (int)c.size()) ? c[k] : mp_integer{0};
    if(ck == 0)
      continue;

    if(k >= (int)n)
    {
      // For k >= n = SF(2^m), any coefficient is fine (Y_k vanishes)
      // Subtract ck * Y_k from c
      for(unsigned j = 0; j <= (unsigned)k && j < Y[k].size(); ++j)
      {
        if(j < c.size())
          c[j] = (c[j] - ck * Y[k][j]) % mod;
      }
    }
    else
    {
      // Check divisibility: b_k = 2^m / gcd(k!, 2^m) must divide c_k
      mp_integer k_fact{1};
      for(int i = 2; i <= k; ++i)
        k_fact *= i;

      unsigned v = nu2(k_fact);
      if(v > m)
        v = m;
      mp_integer bk = mod / power(mp_integer{2}, mp_integer{v});

      if(bk > 0 && ck % bk != 0)
        return false;

      // Subtract ck * Y_k
      for(unsigned j = 0; j <= (unsigned)k && j < Y[k].size(); ++j)
      {
        if(j < c.size())
          c[j] = (c[j] - ck * Y[k][j]) % mod;
      }
    }

    // Reduce and trim
    for(auto &ci : c)
    {
      ci %= mod;
      if(ci < 0)
        ci += mod;
    }
    while(c.size() > 1 && c.back() == 0)
      c.pop_back();
    deg = (int)c.size() - 1;
  }

  return c.size() == 1 && c[0] == 0;
}

bool is_vanishing_polynomial(
  const polynomialt &poly,
  const std::vector<unsigned> &input_widths)
{
  if(poly.is_zero())
    return true;

  unsigned m = poly.bitwidth;

  // Collect all variables used in the polynomial
  std::set<std::size_t> vars_used;
  for(const auto &term : poly.terms)
    for(const auto &[var, exp] : term.second.vars)
      vars_used.insert(var);

  if(vars_used.empty())
  {
    // Constant polynomial: vanishes iff the constant is 0 mod 2^m
    mp_integer mod = power(mp_integer{2}, mp_integer{m});
    return poly.terms[0].first % mod == 0;
  }

  // Univariate case: use the algebraic algorithm
  if(vars_used.size() == 1)
  {
    std::size_t var = *vars_used.begin();
    // Extract coefficients as a vector
    unsigned max_deg = 0;
    for(const auto &term : poly.terms)
      for(const auto &[v, e] : term.second.vars)
        if(v == var && e > max_deg)
          max_deg = e;

    std::vector<mp_integer> coeffs(max_deg + 1, 0);
    for(const auto &term : poly.terms)
    {
      unsigned deg = 0;
      for(const auto &[v, e] : term.second.vars)
        if(v == var)
          deg = e;
      coeffs[deg] += term.first;
    }

    // Use the input width if available, otherwise use m
    unsigned input_w = m;
    if(var < input_widths.size())
      input_w = input_widths[var];

    return is_vanishing_univariate(coeffs, std::min(input_w, m));
  }

  // Multivariate case: use brute-force evaluation if feasible
  mp_integer mod = power(mp_integer{2}, mp_integer{m});
  mp_integer total_inputs{1};
  std::vector<std::pair<std::size_t, unsigned>> var_list;
  for(auto v : vars_used)
  {
    unsigned w = (v < input_widths.size()) ? input_widths[v] : m;
    w = std::min(w, m);
    var_list.push_back(std::make_pair(v, w));
    total_inputs *= power(mp_integer{2}, mp_integer{w});
    if(total_inputs > mp_integer{1} << 24) // 16M limit
      return false; // too many inputs, give up
  }

  // Brute-force evaluate
  std::vector<mp_integer> vals(var_list.size(), 0);
  std::vector<mp_integer> limits(var_list.size());
  for(std::size_t i = 0; i < var_list.size(); ++i)
    limits[i] = power(mp_integer{2}, mp_integer{var_list[i].second});

  for(mp_integer iter{0}; iter < total_inputs; ++iter)
  {
    // Build variable assignment
    std::map<std::size_t, mp_integer> assignment;
    for(std::size_t i = 0; i < var_list.size(); ++i)
      assignment[var_list[i].first] = vals[i];

    // Evaluate polynomial
    mp_integer result{0};
    for(const auto &term : poly.terms)
    {
      mp_integer term_val = term.first;
      for(const auto &[var, exp] : term.second.vars)
      {
        mp_integer v = assignment[var];
        for(unsigned e = 0; e < exp; ++e)
          term_val = (term_val * v) % mod;
      }
      result = (result + term_val) % mod;
    }
    if(result != 0)
      return false;

    // Increment vals
    for(std::size_t i = 0; i < vals.size(); ++i)
    {
      vals[i] += 1;
      if(vals[i] < limits[i])
        break;
      vals[i] = 0;
    }
  }
  return true;
}

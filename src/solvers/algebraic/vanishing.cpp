/// \file
/// Vanishing polynomial test over Z_{2^m}
/// Based on Shekhar, Kalla, Enescu (IEEE TCAD 2007), Theorem 2.

#include "vanishing.h"

#include <util/arith_tools.h>

#include <algorithm>
#include <map>
#include <set>

/// Compute the 2-adic valuation of n
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

/// SF(2^m): smallest k such that 2^m divides k!
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

/// nu2(k!) = sum of nu2(i) for i=1..k
static unsigned nu2_factorial(unsigned k)
{
  unsigned val = 0;
  for(unsigned i = 1; i <= k; ++i)
    val += nu2(mp_integer{i});
  return val;
}

/// A sparse multivariate polynomial over Z_{2^m}, represented as
/// map from exponent-vector to coefficient. The exponent vector
/// is indexed by variable index.
using exponent_key_t = std::map<std::size_t, unsigned>;
using sparse_poly_t = std::map<exponent_key_t, mp_integer>;

/// Convert our polynomialt to sparse_poly_t
static sparse_poly_t to_sparse(const polynomialt &poly)
{
  sparse_poly_t result;
  for(const auto &term : poly.terms)
  {
    exponent_key_t key;
    for(const auto &[var, exp] : term.second.vars)
      key[var] = exp;
    result[key] += term.first;
  }
  // Remove zeros
  for(auto it = result.begin(); it != result.end();)
  {
    if(it->second == 0)
      it = result.erase(it);
    else
      ++it;
  }
  return result;
}

/// Reduce all coefficients mod 2^m
static void reduce_mod(sparse_poly_t &p, const mp_integer &mod)
{
  for(auto it = p.begin(); it != p.end();)
  {
    it->second %= mod;
    if(it->second < 0)
      it->second += mod;
    if(it->second == 0)
      it = p.erase(it);
    else
      ++it;
  }
}

/// Get the maximum degree of variable var in polynomial p
static unsigned max_degree_in(const sparse_poly_t &p, std::size_t var)
{
  unsigned max_deg = 0;
  for(const auto &[key, coeff] : p)
  {
    auto it = key.find(var);
    if(it != key.end() && it->second > max_deg)
      max_deg = it->second;
  }
  return max_deg;
}

/// Extract the "coefficient polynomial" of x_var^deg from p.
/// This is the sum of all terms where x_var has exponent exactly deg,
/// with x_var removed from the monomial.
static sparse_poly_t extract_coeff_of_degree(
  const sparse_poly_t &p,
  std::size_t var,
  unsigned deg)
{
  sparse_poly_t result;
  for(const auto &[key, coeff] : p)
  {
    unsigned var_deg = 0;
    auto it = key.find(var);
    if(it != key.end())
      var_deg = it->second;
    if(var_deg == deg)
    {
      exponent_key_t new_key = key;
      new_key.erase(var);
      if(new_key.empty())
        new_key = exponent_key_t{}; // constant
      result[new_key] += coeff;
    }
  }
  // Remove zeros
  for(auto it = result.begin(); it != result.end();)
  {
    if(it->second == 0)
      it = result.erase(it);
    else
      ++it;
  }
  return result;
}

/// Multiply sparse polynomial by a scalar
static void scale(sparse_poly_t &p, const mp_integer &s, const mp_integer &mod)
{
  for(auto &[key, coeff] : p)
  {
    coeff = (coeff * s) % mod;
    if(coeff < 0)
      coeff += mod;
  }
  // Remove zeros
  for(auto it = p.begin(); it != p.end();)
  {
    if(it->second == 0)
      it = p.erase(it);
    else
      ++it;
  }
}

/// Multiply sparse polynomial by x_var^exp (shift degrees)
static sparse_poly_t shift_var(
  const sparse_poly_t &p,
  std::size_t var,
  unsigned exp)
{
  sparse_poly_t result;
  for(const auto &[key, coeff] : p)
  {
    exponent_key_t new_key = key;
    new_key[var] += exp;
    result[new_key] = coeff;
  }
  return result;
}

/// Subtract q from p (p -= q), reducing mod
static void subtract(sparse_poly_t &p, const sparse_poly_t &q, const mp_integer &mod)
{
  for(const auto &[key, coeff] : q)
  {
    p[key] = (p[key] - coeff) % mod;
    if(p[key] < 0)
      p[key] += mod;
  }
  // Remove zeros
  for(auto it = p.begin(); it != p.end();)
  {
    if(it->second == 0)
      it = p.erase(it);
    else
      ++it;
  }
}

/// Compute falling factorial Y_k(x_var) as a sparse polynomial
static sparse_poly_t falling_factorial(std::size_t var, unsigned k)
{
  // Y_0 = 1, Y_k = (x - (k-1)) * Y_{k-1}
  sparse_poly_t result;
  result[exponent_key_t{}] = 1; // Y_0 = 1

  for(unsigned i = 0; i < k; ++i)
  {
    // Multiply by (x_var - i)
    sparse_poly_t shifted = shift_var(result, var, 1); // x * result
    sparse_poly_t scaled = result;
    scale(scaled, mp_integer{i}, mp_integer{0}); // no mod reduction yet
    // result = shifted - i * result
    result = shifted;
    for(const auto &[key, coeff] : scaled)
      result[key] -= coeff;
    // Remove zeros
    for(auto it = result.begin(); it != result.end();)
    {
      if(it->second == 0)
        it = result.erase(it);
      else
        ++it;
    }
  }
  return result;
}

/// Check if all coefficients of p are divisible by d

bool is_vanishing_polynomial(
  const polynomialt &poly,
  const std::vector<unsigned> &input_widths)
{
  if(poly.is_zero())
    return true;

  unsigned m = poly.bitwidth;
  mp_integer mod = power(mp_integer{2}, mp_integer{m});

  // Convert to sparse representation
  sparse_poly_t p = to_sparse(poly);
  reduce_mod(p, mod);
  if(p.empty())
    return true;

  // Collect all variables
  std::set<std::size_t> vars_used;
  for(const auto &[key, coeff] : p)
    for(const auto &[var, exp] : key)
      vars_used.insert(var);

  if(vars_used.empty())
  {
    // Constant: vanishes iff 0 mod 2^m
    return p.empty();
  }

  unsigned sf = smarandache_function(m);

  // Compute mu_i for each variable
  std::map<std::size_t, unsigned> mu;
  for(auto var : vars_used)
  {
    unsigned ni = m; // default: same as output width
    if(var < input_widths.size() && input_widths[var] > 0)
      ni = input_widths[var];
    unsigned two_ni = (ni >= 30) ? sf : (1u << ni); // avoid overflow
    mu[var] = std::min(two_ni, sf);
  }

  // Phase 1: For each variable i, divide by Y_{mu_i}(x_i).
  // Any polynomial divisible by Y_{mu_i}(x_i) vanishes because
  // x_i ranges over Z_{2^{n_i}} which has only 2^{n_i} values,
  // and Y_{mu_i} evaluated at any of them is divisible by 2^m.
  for(auto var : vars_used)
  {
    unsigned mu_i = mu[var];
    // Repeatedly divide by Y_{mu_i}(x_var) until degree < mu_i
    while(max_degree_in(p, var) >= mu_i)
    {
      unsigned deg = max_degree_in(p, var);
      // The leading coefficient (in x_var) at degree deg
      sparse_poly_t lead = extract_coeff_of_degree(p, var, deg);
      if(lead.empty())
        break;

      // Subtract lead * x_var^{deg - mu_i} * Y_{mu_i}(x_var)
      sparse_poly_t Yk = falling_factorial(var, mu_i);
      // Multiply Yk by x_var^{deg - mu_i}
      sparse_poly_t shifted_Yk = shift_var(Yk, var, deg - mu_i);
      // Multiply by lead (each term of lead * each term of shifted_Yk)
      sparse_poly_t product;
      for(const auto &[lk, lc] : lead)
      {
        for(const auto &[yk, yc] : shifted_Yk)
        {
          exponent_key_t pk = lk;
          for(const auto &[v, e] : yk)
            pk[v] += e;
          product[pk] = (product[pk] + lc * yc) % mod;
        }
      }
      subtract(p, product, mod);
      reduce_mod(p, mod);
    }
  }

  if(p.empty())
    return true;

  // Phase 2: The remaining polynomial must be checked in the falling
  // factorial basis. For univariate, we use the algebraic algorithm.
  // For multivariate, we fall back to brute-force evaluation.
  if(vars_used.size() == 1)
  {
    // Univariate: convert to falling factorial basis and check
    std::size_t var = *vars_used.begin();
    unsigned max_deg = max_degree_in(p, var);
    std::vector<mp_integer> coeffs(max_deg + 1, mp_integer{0});
    for(const auto &[key, coeff] : p)
    {
      unsigned deg = 0;
      auto it = key.find(var);
      if(it != key.end())
        deg = it->second;
      coeffs[deg] += coeff;
    }
    // Use the univariate falling factorial algorithm
    unsigned input_w = m;
    auto mu_it = mu.find(var);
    if(mu_it != mu.end())
    {
      unsigned ni = m;
      if(var < input_widths.size() && input_widths[var] > 0)
        ni = input_widths[var];
      input_w = std::min(ni, m);
    }
    // Build falling factorials and check divisibility
    unsigned sf_w = smarandache_function(input_w);
    // Convert to falling factorial basis by iterative extraction
    for(int k = (int)max_deg; k >= 0; --k)
    {
      mp_integer ck = (k < (int)coeffs.size()) ? (coeffs[k] % mod) : mp_integer{0};
      if(ck < 0) ck += mod;
      if(ck == 0) continue;

      if((unsigned)k >= sf_w)
      {
        // Y_k vanishes, subtract ck * Y_k
        auto ff = falling_factorial(var, k);
        for(const auto &[fk, fc] : ff)
        {
          unsigned deg = 0;
          auto it = fk.find(var);
          if(it != fk.end()) deg = it->second;
          if(deg < coeffs.size())
            coeffs[deg] = (coeffs[deg] - ck * fc) % mod;
        }
      }
      else
      {
        unsigned total_v = nu2_factorial(k);
        unsigned gcd_v = std::min(m, total_v);
        unsigned bk_exp = m - gcd_v;
        if(bk_exp > 0)
        {
          mp_integer bk = power(mp_integer{2}, mp_integer{bk_exp});
          if(ck % bk != 0) return false;
        }
        // Subtract ck * Y_k
        auto ff = falling_factorial(var, k);
        for(const auto &[fk, fc] : ff)
        {
          unsigned deg = 0;
          auto it = fk.find(var);
          if(it != fk.end()) deg = it->second;
          if(deg < coeffs.size())
            coeffs[deg] = (coeffs[deg] - ck * fc) % mod;
        }
      }
    }
    // Check if all coefficients are zero
    for(const auto &c : coeffs)
      if(c % mod != 0) return false;
    return true;
  }

  // Multivariate: brute-force evaluation
  mp_integer total_inputs{1};
  std::vector<std::pair<std::size_t, unsigned>> var_list;
  for(auto v : vars_used)
  {
    unsigned w = (v < input_widths.size() && input_widths[v] > 0)
                   ? input_widths[v] : m;
    w = std::min(w, m);
    var_list.push_back(std::make_pair(v, w));
    total_inputs *= power(mp_integer{2}, mp_integer{w});
    if(total_inputs > (mp_integer{1} << 24))
      return false; // too many inputs
  }

  std::vector<mp_integer> vals(var_list.size(), mp_integer{0});
  std::vector<mp_integer> limits(var_list.size());
  for(std::size_t i = 0; i < var_list.size(); ++i)
    limits[i] = power(mp_integer{2}, mp_integer{var_list[i].second});

  for(mp_integer iter{0}; iter < total_inputs; ++iter)
  {
    std::map<std::size_t, mp_integer> assignment;
    for(std::size_t i = 0; i < var_list.size(); ++i)
      assignment[var_list[i].first] = vals[i];

    mp_integer result{0};
    for(const auto &[key, coeff] : p)
    {
      mp_integer term_val = coeff;
      for(const auto &[var, exp] : key)
      {
        mp_integer v = assignment[var];
        for(unsigned e = 0; e < exp; ++e)
          term_val = (term_val * v) % mod;
      }
      result = (result + term_val) % mod;
    }
    if(result != 0)
      return false;

    for(std::size_t i = 0; i < vals.size(); ++i)
    {
      vals[i] += 1;
      if(vals[i] < limits[i]) break;
      vals[i] = 0;
    }
  }
  return true;
}

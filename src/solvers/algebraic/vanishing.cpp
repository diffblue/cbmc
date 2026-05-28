/// \file
/// Vanishing polynomial test over Z_{2^m}
/// Based on Shekhar, Kalla, Enescu (IEEE TCAD 2007) and
/// Gàmez-Montolio, Florit, Brain, Howe (BAR 2024) Algorithm 3.

#include "vanishing.h"

#include <util/arith_tools.h>

#include <algorithm>
#include <map>
#include <set>
#include <vector>

/// 2-adic valuation of n
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

/// nu2(k!)
static unsigned nu2_factorial(unsigned k)
{
  unsigned val = 0;
  for(unsigned i = 1; i <= k; ++i)
    val += nu2(mp_integer{i});
  return val;
}





/// Multivariate monomial key: vector of exponents
using mono_key_t = std::vector<unsigned>;

/// Sparse multivariate polynomial: map from exponent vector to coefficient
using sparse_poly_t = std::map<mono_key_t, mp_integer>;



/// Build the Stirling numbers of the second kind S(n,k) mod 2^m.
/// S(n,k) counts the number of partitions of {1,...,n} into k blocks.
/// The canonical→factorial conversion uses: u[k] = sum_n v[n] * S(n,k),
/// i.e., the conversion matrix is the TRANSPOSE of the Stirling matrix.
/// We return the transposed matrix directly: result[k][n] = S(n,k).
static std::vector<std::vector<mp_integer>>
build_canonical_to_factorial(unsigned d, const mp_integer &mod)
{
  // Build S(n,k) for 0 <= n,k <= d
  // Recurrence: S(0,0)=1, S(n,k) = k*S(n-1,k) + S(n-1,k-1)
  std::vector<std::vector<mp_integer>> S(d + 1, std::vector<mp_integer>(d + 1, 0));
  S[0][0] = 1;
  for(unsigned n = 1; n <= d; ++n)
    for(unsigned k = 1; k <= n; ++k)
      S[n][k] = (k * S[n - 1][k] + S[n - 1][k - 1]) % mod;

  // Return S directly: S[n][k] = Stirling number of second kind.
  // The conversion is u[k] = sum_n S[n][k] * v[n], i.e., u = S^T * v.
  // The Kronecker product uses S[col][row] for each variable.
  return S;
}

/// Compute one entry of F^{⊗k}: F^{⊗k}_{r,c} = ∏_i F[r_i][c_i]
static mp_integer kronecker_entry(
  const std::vector<std::vector<mp_integer>> &F,
  const std::vector<unsigned> &row_exps,
  const std::vector<unsigned> &col_exps,
  const mp_integer &mod)
{
  mp_integer result = 1;
  for(std::size_t i = 0; i < row_exps.size(); ++i)
  {
    unsigned r = row_exps[i]; // factorial index k
    unsigned c = col_exps[i]; // canonical index n
    // F is S[n][k], so we need F[c][r] = S(c, r)
    if(c >= F.size() || r >= F[0].size())
      return 0;
    result = (result * F[c][r]) % mod;
    if(result == 0)
      return 0;
  }
  return result;
}

/// Multivariate monomial key
using mono_key_t = std::vector<unsigned>;
/// Sparse multivariate polynomial
using sparse_poly_t = std::map<mono_key_t, mp_integer>;

// PROOF: formal-proofs/Vanishing.lean::fallingFactorial_zero_of_lt
//        Soundness: (x)_n = 0 for x < n (the falling factorial
//        vanishes on the integers up to its degree).
// PROOF: formal-proofs/Vanishing.lean::falling_factorial_sufficient
//        Soundness: a polynomial reducing to 0 modulo the falling
//        factorial vanishes on [0, n).
bool is_vanishing_polynomial(
  const polynomialt &poly,
  const std::vector<unsigned> &input_widths)
{
  if(poly.is_zero())
    return true;

  unsigned m = poly.bitwidth;
  mp_integer mod = power(mp_integer{2}, mp_integer{m});

  // Collect variables and max degree
  std::set<std::size_t> vars_used;
  for(const auto &term : poly.terms)
    for(const auto &[var, exp] : term.second.vars)
      vars_used.insert(var);

  if(vars_used.empty())
  {
    mp_integer c = poly.terms.empty() ? mp_integer{0} : poly.terms[0].first;
    return c % mod == 0;
  }

  // Map variable indices to 0..k-1
  std::vector<std::size_t> var_list(vars_used.begin(), vars_used.end());
  unsigned k = var_list.size();
  std::map<std::size_t, unsigned> var_to_idx;
  for(unsigned i = 0; i < k; ++i)
    var_to_idx[var_list[i]] = i;

  // Find max degree in any variable
  unsigned max_deg = 0;
  for(const auto &term : poly.terms)
    for(const auto &[var, exp] : term.second.vars)
      if(exp > max_deg)
        max_deg = exp;

  unsigned sf = smarandache_function(m);
  // d_w: the max degree we need to consider
  unsigned dw = sf; // d_w = SF(2^m) for same-width case

  // Clamp max_deg to dw (higher terms vanish)
  unsigned d = std::min(max_deg, dw);

  // Build univariate F matrix of size (d+1) x (max_deg+1)
  unsigned mat_size = std::max(d + 1, max_deg + 1);
  auto F = build_canonical_to_factorial(mat_size, mod);

  // Convert polynomial to sparse form with remapped variables
  sparse_poly_t p;
  for(const auto &term : poly.terms)
  {
    mono_key_t key(k, 0);
    for(const auto &[var, exp] : term.second.vars)
    {
      auto it = var_to_idx.find(var);
      if(it != var_to_idx.end())
        key[it->second] = exp;
    }
    p[key] = (p[key] + term.first) % mod;
    if(p[key] < 0)
      p[key] += mod;
  }
  for(auto it = p.begin(); it != p.end();)
  {
    if(it->second == 0)
      it = p.erase(it);
    else
      ++it;
  }

  if(p.empty())
    return true;

  // Algorithm 3: Convert to factorial basis using Kronecker product
  // u = F^{⊗k} · v_P (sparse multiplication)
  // For each nonzero entry v_P[c], compute the c-th column of F^{⊗k}
  // and accumulate into u.

  // Enumerate all possible factorial-basis monomials up to degree d in each var
  // u[row_exps] = sum over nonzero p[col_exps] of F^{⊗k}_{row,col} * p[col]
  sparse_poly_t u; // factorial basis coefficients

  for(const auto &[col_exps, coeff] : p)
  {
    if(coeff == 0)
      continue;

    // For this column, compute all rows of F^{⊗k} that could be nonzero.
    // F[r][c] is nonzero only when r >= c (lower triangular).
    // So row_exps[i] >= col_exps[i] for all i.
    // Enumerate all row_exps with row_exps[i] in [col_exps[i], d].

    // Use recursive enumeration over variables
    std::function<void(unsigned, mono_key_t &)> enumerate =
      [&](unsigned var_idx, mono_key_t &row) {
        if(var_idx == k)
        {
          mp_integer entry = kronecker_entry(F, row, col_exps, mod);
          if(entry != 0)
            u[row] = (u[row] + entry * coeff) % mod;
          return;
        }
        unsigned lo = 0;
        unsigned hi = std::min(d, mat_size - 1);
        for(unsigned e = lo; e <= hi; ++e)
        {
          row[var_idx] = e;
          enumerate(var_idx + 1, row);
        }
      };

    mono_key_t row(k, 0);
    enumerate(0, row);
  }

  // Reduce coefficients: u[j] %= c_{j1,...,jk}
  // c_j = 2^{max(w - sum_i nu2(ji!), 0)}
  for(auto it = u.begin(); it != u.end();)
  {
    it->second %= mod;
    if(it->second < 0)
      it->second += mod;

    if(it->second != 0)
    {
      const auto &exps = it->first;
      unsigned total_nu2 = 0;
      for(unsigned i = 0; i < k; ++i)
      {
        // Use actual input width for mu_i calculation
        unsigned ni = m;
        if(var_list[i] < input_widths.size() && input_widths[var_list[i]] > 0)
          ni = input_widths[var_list[i]];
        unsigned mu_i = std::min((ni >= 30) ? sf : (1u << ni), sf);
        if(exps[i] >= mu_i)
        {
          // This term vanishes (degree >= mu_i in variable i)
          it->second = 0;
          break;
        }
        total_nu2 += nu2_factorial(exps[i]);
      }

      if(it->second != 0)
      {
        unsigned gcd_nu2 = std::min(m, total_nu2);
        unsigned cj_exp = m - gcd_nu2;
        if(cj_exp > 0)
        {
          mp_integer cj = power(mp_integer{2}, mp_integer{cj_exp});
          it->second %= cj;
        }
        // If cj_exp == 0, cj = 1, any value is fine (term vanishes)
        else
        {
          it->second = 0;
        }
      }
    }

    if(it->second == 0)
      it = u.erase(it);
    else
      ++it;
  }

  return u.empty();
}

/// Build the univariate falling factorial $x^{\underline{k}}$ as a
/// polynomial in variable \p var_idx over $\mathbb{Z}_{2^d}$, scaled
/// by an integer \p coeff.
///
/// $x^{\underline{k}} = x \cdot (x-1) \cdot (x-2) \cdots (x-k+1)$.
/// $x^{\underline{0}} = 1$ by convention.
static polynomialt build_falling_factorial(
  unsigned d,
  std::size_t var_idx,
  unsigned k,
  const mp_integer &coeff)
{
  polynomialt result{d, coeff};
  for(unsigned i = 0; i < k; ++i)
  {
    polynomialt factor{d, mp_integer{1}, var_idx};
    factor = factor - polynomialt{d, mp_integer{i}};
    result = result * factor;
  }
  result.normalize();
  return result;
}

std::vector<polynomialt>
generate_zfp_generators(unsigned d, std::size_t var_idx, unsigned input_width)
{
  std::vector<polynomialt> result;

  // Smarandache function SF(2^d) gives the smallest k with nu2(k!) >= d.
  unsigned sf = smarandache_function(d);

  // Effective max k for the standard generators.
  unsigned max_k = sf;

  // If input is narrower than d, x ranges over {0, ..., 2^n - 1}.
  // Then x^{\underline{2^n}} = x(x-1)...(x-(2^n-1)) is identically
  // zero on the input range. Use this if it is smaller than SF.
  if(input_width > 0 && input_width < 30)
  {
    unsigned input_range = 1u << input_width;
    if(input_range < max_k)
      max_k = input_range;
  }

  // Skip k=1: 2^d * x = 0 mod 2^d, vacuous.
  for(unsigned k = 2; k <= max_k; ++k)
  {
    unsigned val_k = nu2_factorial(k);
    mp_integer coeff;
    if(val_k >= d)
      coeff = mp_integer{1};
    else
      coeff = power(mp_integer{2}, mp_integer{d - val_k});

    polynomialt zfp = build_falling_factorial(d, var_idx, k, coeff);
    if(!zfp.is_zero())
      result.push_back(std::move(zfp));
  }

  return result;
}

/// \file
/// Extract polynomial equations from CBMC expression trees

#include "poly_extract.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mp_arith.h>
#include <util/std_expr.h>

bool poly_extractort::set_bitwidth(const typet &type)
{
  unsigned bw = 0;
  if(type.id() == ID_unsignedbv)
    bw = to_unsignedbv_type(type).get_width();
  else if(type.id() == ID_signedbv)
    bw = to_signedbv_type(type).get_width();
  else
    return false;

  if(bitwidth == 0)
  {
    bitwidth = bw;
    return true;
  }
  // Accept same width or wider (for extractbits of wider expressions).
  // Polynomial arithmetic mod 2^bitwidth automatically handles the
  // wider intermediate values.
  return bw >= bitwidth;
}

std::size_t poly_extractort::get_var_index(const irep_idt &name)
{
  auto [it, inserted] = var_map.emplace(name, next_var_index);
  if(inserted)
  {
    reverse_var_map[next_var_index] = name;
    ++next_var_index;
  }
  return it->second;
}

std::optional<polynomialt> poly_extractort::to_polynomial(const exprt &e)
{
  if(!set_bitwidth(e.type()))
    return std::nullopt;

  // Constant
  if(e.is_constant())
  {
    if(!set_bitwidth(e.type()))
      return std::nullopt;
    auto val = numeric_cast<mp_integer>(e);
    if(!val.has_value())
      return std::nullopt;
    return polynomialt{bitwidth, *val};
  }

  // Symbol (SSA variable)
  if(e.id() == ID_symbol)
  {
    if(!set_bitwidth(e.type()))
      return std::nullopt;
    std::size_t idx = get_var_index(to_symbol_expr(e).get_identifier());
    return polynomialt{bitwidth, mp_integer{1}, idx};
  }

  // Typecast — handle widening/narrowing between bitvector types
  if(e.id() == ID_typecast)
  {
    if(!set_bitwidth(e.type()))
      return std::nullopt;
    return to_polynomial(to_typecast_expr(e).op());
  }

  // Zero-extend: same value, wider type — treat as identity.
  // Set bitwidth from the outer (wider) type first, so that the
  // inner expression's polynomial uses the correct ring.
  if(e.id() == ID_zero_extend)
  {
    if(!set_bitwidth(e.type()))
      return std::nullopt;
    unsigned saved_bw = bitwidth;
    bitwidth = 0; // allow inner expression to set its own width
    auto result = to_polynomial(to_zero_extend_expr(e).op());
    bitwidth = saved_bw; // restore outer width
    if(result && inline_products)
    {
      auto inner_width = to_bitvector_type(
        to_zero_extend_expr(e).op().type()).get_width();
      for(const auto &term : result->terms)
        for(const auto &[var, exp] : term.second.vars)
          if(var_input_widths.find(var) == var_input_widths.end())
            var_input_widths[var] = inner_width;
    }
    // Ensure the polynomial uses the outer bitwidth
    if(result && result->bitwidth < bitwidth)
      result->bitwidth = bitwidth;
    return result;
  }

  // Extract bits: extract(x, hi, lo) extracts bits hi..lo.
  // When lo=0 and the result width matches our polynomial ring,
  // this is x mod 2^bw — just convert x in our ring.
  // When the source is wider, we convert the source's subexpressions
  // in our (narrower) ring, which automatically reduces mod 2^bw.
  if(e.id() == ID_extractbits)
  {
    // extract(x, hi, lo): only handle when lo=0 (low-bit extraction).
    // extract(x, bw-1, 0) = x mod 2^bw, which is just x in our ring.
    // extract with lo>0 is a shift, which is non-polynomial.
    const auto &eb = to_extractbits_expr(e);
    if(eb.index().is_constant())
    {
      auto lo = numeric_cast<mp_integer>(eb.index());
      if(lo.has_value() && *lo != 0)
        return std::nullopt; // non-zero low index = shift
    }
    if(!set_bitwidth(e.type()))
      return std::nullopt;
    unsigned saved_bw = bitwidth;
    auto result = to_polynomial(eb.src());
    bitwidth = saved_bw;
    return result;
  }

  // Addition: a + b
  if(e.id() == ID_plus)
  {
    if(e.operands().size() < 2)
      return std::nullopt;
    auto result = to_polynomial(e.operands()[0]);
    if(!result)
      return std::nullopt;
    for(std::size_t i = 1; i < e.operands().size(); ++i)
    {
      auto op = to_polynomial(e.operands()[i]);
      if(!op)
        return std::nullopt;
      result = *result + *op;
    }
    return result;
  }

  // Subtraction: a - b
  if(e.id() == ID_minus)
  {
    if(e.operands().size() != 2)
      return std::nullopt;
    auto lhs = to_polynomial(to_minus_expr(e).lhs());
    auto rhs = to_polynomial(to_minus_expr(e).rhs());
    if(!lhs || !rhs)
      return std::nullopt;
    return *lhs - *rhs;
  }

  // Unary minus: -a
  if(e.id() == ID_unary_minus)
  {
    auto op = to_polynomial(to_unary_minus_expr(e).op());
    if(!op)
      return std::nullopt;
    return *op * mp_integer{-1};
  }

  // Multiplication: a * b
  // For inline expressions (not SSA), introduce a fresh variable for
  // the product and add a side equation: fresh - a*b = 0.
  // This enables the Gröbner basis to reason about the multiplication
  // algebraically even when there are no SSA intermediate variables.
  if(e.id() == ID_mult)
  {
    if(e.operands().size() < 2)
      return std::nullopt;
    auto result = to_polynomial(e.operands()[0]);
    if(!result)
      return std::nullopt;
    for(std::size_t i = 1; i < e.operands().size(); ++i)
    {
      auto op = to_polynomial(e.operands()[i]);
      if(!op)
        return std::nullopt;
      polynomialt product = *result * *op;
      // Only introduce a fresh variable when both factors are
      // non-constant (genuine symbolic multiplication). For scalar
      // multiplication (a * 5), return the product directly.
      if(result->is_constant() || op->is_constant() || inline_products)
      {
        result = product;
      }
      else
      {
        unsigned bw = product.bitwidth;
        std::size_t fresh_idx =
          get_var_index("__fresh_mul_" + std::to_string(next_fresh++));
        polynomialt fresh_var{bw, mp_integer{1}, fresh_idx};
        side_equations.push_back(fresh_var - product);
        result = fresh_var;
      }
    }
    return result;
  }

  // Left shift by constant: a << k = a * 2^k
  if(
    e.id() == ID_shl && e.operands().size() == 2 &&
    e.operands()[1].is_constant())
  {
    auto base = to_polynomial(e.operands()[0]);
    if(!base)
      return std::nullopt;
    auto shift_amt = numeric_cast<mp_integer>(e.operands()[1]);
    if(!shift_amt || *shift_amt < 0)
      return std::nullopt;
    mp_integer factor = power(mp_integer{2}, *shift_amt);
    return *base * factor;
  }

  // Right shift by constant: a >> k.
  //
  // bvlshr is not a polynomial operation in Z_{2^d}, but it becomes
  // one once we expose the bit-level structure of a via
  // bit-decomposition variables b_{a,0}, ..., b_{a,d-1}:
  //
  //   a >> k = sum_{i = k}^{d-1} 2^{i-k} b_{a,i}
  //
  // The bit variables and the side equations enforcing idempotency
  // and sum-decomposition are managed by decompose_bits(), which
  // caches per host-variable index to avoid duplicate constraints.
  //
  // Sound by construction: the bit-decomposition encoding uniquely
  // determines b_{a,i} given a, so the augmented system has the
  // same models as the original (extended by the bit witnesses).
  if(
    e.id() == ID_lshr && e.operands().size() == 2 &&
    e.operands()[1].is_constant())
  {
    if(!set_bitwidth(e.type()))
      return std::nullopt;
    auto shift_amt = numeric_cast<mp_integer>(e.operands()[1]);
    if(!shift_amt || *shift_amt < 0)
      return std::nullopt;
    unsigned d = bitwidth;
    if(*shift_amt >= mp_integer{d})
    {
      // a >> k for k >= d is 0 (in unsigned bit-vectors).
      return polynomialt{d};
    }
    auto bits = decompose_bits(e.operands()[0]);
    if(!bits)
      return std::nullopt;
    unsigned k = static_cast<unsigned>(shift_amt->to_long());
    polynomialt result{d};
    std::set<std::size_t> bit_vars = get_bit_var_indices();
    for(unsigned i = k; i < d; ++i)
    {
      mp_integer coeff = power(mp_integer{2}, mp_integer{i - k});
      result = result + (*bits)[i] * coeff;
    }
    result.normalize();
    apply_frobenius_idempotency(result, bit_vars);
    return result;
  }

  // Bitwise NOT: ~a = sum_i 2^i (1 - b_{a,i}).
  // Sound via bit-decomposition (same construction as bvlshr).
  if(e.id() == ID_bitnot && e.operands().size() == 1)
  {
    if(!set_bitwidth(e.type()))
      return std::nullopt;
    auto bits = decompose_bits(e.operands()[0]);
    if(!bits)
      return std::nullopt;
    unsigned d = bitwidth;
    polynomialt one{d, mp_integer{1}};
    polynomialt result{d};
    std::set<std::size_t> bit_vars = get_bit_var_indices();
    for(unsigned i = 0; i < d; ++i)
    {
      mp_integer coeff = power(mp_integer{2}, mp_integer{i});
      polynomialt not_bit = one - (*bits)[i];
      result = result + not_bit * coeff;
    }
    result.normalize();
    apply_frobenius_idempotency(result, bit_vars);
    return result;
  }

  // Bitwise AND: a & b = sum_i 2^i (b_{a,i} * b_{b,i}).
  // Sound via bit-decomposition. The product b_{a,i} * b_{b,i} is a
  // degree-2 polynomial in the bit variables, faithfully modelling
  // the bitwise AND of a and b.
  if(
    (e.id() == ID_bitand || e.id() == ID_bitor || e.id() == ID_bitxor) &&
    e.operands().size() >= 2)
  {
    if(!set_bitwidth(e.type()))
      return std::nullopt;
    unsigned d = bitwidth;
    auto acc_bits = decompose_bits(e);
    if(!acc_bits)
      return std::nullopt;
    polynomialt result{d};
    std::set<std::size_t> bit_vars = get_bit_var_indices();
    for(unsigned j = 0; j < d; ++j)
    {
      mp_integer coeff = power(mp_integer{2}, mp_integer{j});
      result = result + (*acc_bits)[j] * coeff;
    }
    result.normalize();
    apply_frobenius_idempotency(result, bit_vars);
    return result;
  }

  // if-then-else: ite(cond, a, 0) = cond * a (when cond is 0/1)
  if(e.id() == ID_if && e.operands().size() == 3)
  {
    const auto &cond = to_if_expr(e).cond();
    const auto &true_val = to_if_expr(e).true_case();
    const auto &false_val = to_if_expr(e).false_case();

    // ite(cond, a, 0): check if false branch is zero
    if(false_val.is_constant())
    {
      auto fv = numeric_cast<mp_integer>(false_val);
      if(fv && *fv == 0)
      {
        // cond must be a boolean (0 or 1) — model as a variable
        auto cond_poly = to_polynomial(cond);
        auto true_poly = to_polynomial(true_val);
        if(cond_poly && true_poly)
          return *cond_poly * *true_poly;
      }
    }
    // ite(cond, 0, b): check if true branch is zero
    if(true_val.is_constant())
    {
      auto tv = numeric_cast<mp_integer>(true_val);
      if(tv && *tv == 0)
      {
        auto cond_poly = to_polynomial(cond);
        auto false_poly = to_polynomial(false_val);
        if(cond_poly && false_poly)
        {
          // ite(cond, 0, b) = (1 - cond) * b
          polynomialt one{false_poly->bitwidth, mp_integer{1}};
          return (one - *cond_poly) * *false_poly;
        }
      }
    }
  }

  // Boolean equality: (a == b) as a 1-bit value
  // In polynomial terms: 1 - (a - b)^2 ... no, that's not right.
  // For single-bit: (extract(b, i, i) == 1) is just extract(b, i, i).
  // Model boolean comparisons as variables.
  if(e.id() == ID_equal && e.type().id() == ID_bool)
  {
    // Check if this is (extract(b, i, i) == 1)
    const auto &eq = to_equal_expr(e);
    if(eq.rhs().is_constant())
    {
      auto rhs_val = numeric_cast<mp_integer>(eq.rhs());
      if(rhs_val && *rhs_val == 1)
        return to_polynomial(eq.lhs());
    }
    if(eq.lhs().is_constant())
    {
      auto lhs_val = numeric_cast<mp_integer>(eq.lhs());
      if(lhs_val && *lhs_val == 1)
        return to_polynomial(eq.rhs());
    }
  }

  // Single-bit extractbits: extract(b, i, i) — model as a variable
  // with the implicit constraint that it's 0 or 1.
  // (The 0/1 constraint is not added — the Gröbner basis treats it
  // as a free variable. This is sound for UNSAT checking because
  // if the system is UNSAT for free variables, it's UNSAT for 0/1.)

  // Anything else (bitwise ops, shifts, division, etc.) is non-polynomial
  return std::nullopt;
}

std::optional<polynomialt> poly_extractort::extract_equation(const exprt &eq)
{
  if(eq.id() != ID_equal || eq.operands().size() != 2)
    return std::nullopt;

  const auto &equal = to_equal_expr(eq);
  auto lhs = to_polynomial(equal.lhs());
  auto rhs = to_polynomial(equal.rhs());
  if(!lhs || !rhs)
    return std::nullopt;

  polynomialt diff = *lhs - *rhs;
  diff.normalize();
  return diff;
}

std::optional<std::vector<polynomialt>>
poly_extractort::decompose_bits(const exprt &e)
{
  // Determine the polynomial bitwidth d from the expression's type.
  if(!set_bitwidth(e.type()))
    return std::nullopt;
  unsigned d = bitwidth;
  if(d == 0)
    return std::nullopt;

  // Constants: the bits of a constant are computable directly.
  if(e.is_constant())
  {
    auto val = numeric_cast<mp_integer>(e);
    if(!val.has_value())
      return std::nullopt;
    std::vector<polynomialt> bits;
    bits.reserve(d);
    mp_integer v = *val;
    if(v < 0)
      v += power(mp_integer{2}, mp_integer{d});
    for(unsigned i = 0; i < d; ++i)
    {
      bool bit_set = (v / power(mp_integer{2}, mp_integer{i})) % 2 != 0;
      bits.emplace_back(d, mp_integer{bit_set ? 1 : 0});
    }
    return bits;
  }

  // bvnot a: bit i is (1 - bit_a_i). Avoids fresh host.
  if(e.id() == ID_bitnot && e.operands().size() == 1)
  {
    auto inner_bits = decompose_bits(e.operands()[0]);
    if(!inner_bits)
      return std::nullopt;
    std::vector<polynomialt> result;
    result.reserve(d);
    polynomialt one{d, mp_integer{1}};
    for(const auto &b : *inner_bits)
      result.push_back(one - b);
    return result;
  }

  // bvshl a k (constant k): bit i is bit_a_{i-k} for i >= k, else 0.
  if(
    e.id() == ID_shl && e.operands().size() == 2 &&
    e.operands()[1].is_constant())
  {
    auto shift_amt = numeric_cast<mp_integer>(e.operands()[1]);
    if(!shift_amt || *shift_amt < 0)
      return std::nullopt;
    auto inner_bits = decompose_bits(e.operands()[0]);
    if(!inner_bits)
      return std::nullopt;
    std::vector<polynomialt> result;
    result.reserve(d);
    polynomialt zero{d};
    if(*shift_amt >= mp_integer{d})
    {
      for(unsigned i = 0; i < d; ++i)
        result.push_back(zero);
      return result;
    }
    unsigned k = static_cast<unsigned>(shift_amt->to_long());
    for(unsigned i = 0; i < d; ++i)
    {
      if(i < k)
        result.push_back(zero);
      else
        result.push_back((*inner_bits)[i - k]);
    }
    return result;
  }

  // bvlshr a k (constant k): bit i is bit_a_{i+k} for i < d-k, else 0.
  if(
    e.id() == ID_lshr && e.operands().size() == 2 &&
    e.operands()[1].is_constant())
  {
    auto shift_amt = numeric_cast<mp_integer>(e.operands()[1]);
    if(!shift_amt || *shift_amt < 0)
      return std::nullopt;
    auto inner_bits = decompose_bits(e.operands()[0]);
    if(!inner_bits)
      return std::nullopt;
    std::vector<polynomialt> result;
    result.reserve(d);
    polynomialt zero{d};
    if(*shift_amt >= mp_integer{d})
    {
      for(unsigned i = 0; i < d; ++i)
        result.push_back(zero);
      return result;
    }
    unsigned k = static_cast<unsigned>(shift_amt->to_long());
    for(unsigned i = 0; i < d; ++i)
    {
      if(i + k < d)
        result.push_back((*inner_bits)[i + k]);
      else
        result.push_back(zero);
    }
    return result;
  }

  // bvand / bvor / bvxor: combine bits pairwise without fresh host.
  if(
    (e.id() == ID_bitand || e.id() == ID_bitor || e.id() == ID_bitxor) &&
    e.operands().size() >= 2)
  {
    auto acc = decompose_bits(e.operands()[0]);
    if(!acc)
      return std::nullopt;
    // Snapshot bit-var set for eager Frobenius reduction. Each
    // multiplication below can produce b_i^k for k >= 2; clamping
    // immediately keeps polynomials small.
    std::set<std::size_t> bit_vars = get_bit_var_indices();
    for(std::size_t k = 1; k < e.operands().size(); ++k)
    {
      auto next = decompose_bits(e.operands()[k]);
      if(!next)
        return std::nullopt;
      // Refresh bit-var set: decompose_bits may have added more.
      bit_vars = get_bit_var_indices();
      std::vector<polynomialt> combined;
      combined.reserve(d);
      for(unsigned j = 0; j < d; ++j)
      {
        const polynomialt &x = (*acc)[j];
        const polynomialt &y = (*next)[j];
        polynomialt bit{d};
        if(e.id() == ID_bitand)
          bit = x.multiply(y, bit_vars);
        else if(e.id() == ID_bitor)
          bit = (x + y) - x.multiply(y, bit_vars);
        else // ID_bitxor
          bit = (x + y) - x.multiply(y, bit_vars) * mp_integer{2};
        apply_frobenius_idempotency(bit, bit_vars);
        combined.push_back(std::move(bit));
      }
      acc = std::move(combined);
    }
    return acc;
  }

  // Fallback: convert to a polynomial via to_polynomial, attach a
  // fresh host variable, and decompose that. This is the original
  // implementation; it handles arbitrary polynomial expressions
  // (sums, differences, products) by introducing a fresh host h
  // with the equation h = poly and then decomposing h into bit
  // variables.
  auto host_poly = to_polynomial(e);
  if(!host_poly)
    return std::nullopt;

  // If the polynomial is a single variable (1 * x_v + 0), we use that
  // variable as the host directly. Otherwise, check the polynomial-
  // form cache: two syntactically-different-but-semantically-equal
  // polynomials (e.g., a+b and b+a) normalise to the same polynomial
  // and should share a host. Only if the polynomial form has not
  // been seen before do we introduce a fresh host.
  std::size_t host_idx;
  if(
    host_poly->terms.size() == 1 &&
    host_poly->terms.front().first == mp_integer{1} &&
    host_poly->terms.front().second.vars.size() == 1 &&
    host_poly->terms.front().second.vars.front().second == 1)
  {
    host_idx = host_poly->terms.front().second.vars.front().first;
  }
  else
  {
    // Build a canonical key for this polynomial form.
    std::string key;
    for(const auto &[coeff, mono] : host_poly->terms)
    {
      key += integer2string(coeff) + ":";
      for(const auto &[var, exp] : mono.vars)
        key += std::to_string(var) + "^" + std::to_string(exp) + ",";
      key += ";";
    }
    auto pit = poly_host_cache.find(key);
    if(pit != poly_host_cache.end())
    {
      host_idx = pit->second;
    }
    else
    {
      host_idx = get_var_index("__bd_host_" + std::to_string(next_fresh++));
      polynomialt host_var{d, mp_integer{1}, host_idx};
      polynomialt host_eq = host_var - *host_poly;
      host_eq.normalize();
      if(!host_eq.is_zero())
        side_equations.push_back(std::move(host_eq));
      poly_host_cache.emplace(std::move(key), host_idx);
    }
  }

  // Cache check: if the host has been decomposed already, return the
  // cached bit polynomials without adding new side equations.
  auto cache_it = bit_decomp_cache.find(host_idx);
  if(cache_it != bit_decomp_cache.end())
  {
    std::vector<polynomialt> bits;
    bits.reserve(cache_it->second.size());
    for(std::size_t b_idx : cache_it->second)
      bits.emplace_back(d, mp_integer{1}, b_idx);
    return bits;
  }

  // Allocate d fresh bit variables and add side equations.
  std::vector<std::size_t> bit_indices;
  bit_indices.reserve(d);
  std::vector<polynomialt> bits;
  bits.reserve(d);
  for(unsigned i = 0; i < d; ++i)
  {
    std::size_t b_idx = get_var_index(
      "__bd_bit_" + std::to_string(host_idx) + "_" + std::to_string(i));
    bit_indices.push_back(b_idx);
    polynomialt b{d, mp_integer{1}, b_idx};

    // Idempotency: b^2 - b = 0
    polynomialt idem = (b * b) - b;
    idem.normalize();
    if(!idem.is_zero())
      side_equations.push_back(std::move(idem));

    bits.push_back(std::move(b));
  }

  // Sum-decomposition: host - sum_i 2^i * b_i = 0
  polynomialt host_var{d, mp_integer{1}, host_idx};
  polynomialt sum{d};
  for(unsigned i = 0; i < d; ++i)
  {
    mp_integer coeff = power(mp_integer{2}, mp_integer{i});
    sum = sum + bits[i] * coeff;
  }
  polynomialt sum_eq = host_var - sum;
  sum_eq.normalize();
  if(!sum_eq.is_zero())
    side_equations.push_back(std::move(sum_eq));

  bit_decomp_cache.emplace(host_idx, std::move(bit_indices));
  return bits;
}

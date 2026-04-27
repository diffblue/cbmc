/// \file
/// Extract polynomial equations from CBMC expression trees

#include "poly_extract.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
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
  // Don't set bitwidth from the wider type; keep the narrower ring.
  if(e.id() == ID_zero_extend)
  {
    return to_polynomial(to_zero_extend_expr(e).op());
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
      if(result->is_constant() || op->is_constant())
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

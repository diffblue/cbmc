/// \file
/// Extract polynomial equations from CBMC expression trees

#include "poly_extract.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>

bool poly_extractort::set_bitwidth(const typet &type)
{
  if(type.id() == ID_unsignedbv)
  {
    unsigned bw = to_unsignedbv_type(type).get_width();
    if(bitwidth == 0)
      bitwidth = bw;
    return bitwidth == bw;
  }
  if(type.id() == ID_signedbv)
  {
    unsigned bw = to_signedbv_type(type).get_width();
    if(bitwidth == 0)
      bitwidth = bw;
    return bitwidth == bw;
  }
  return false;
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
  if(bitwidth == 0 && !set_bitwidth(e.type()))
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
      // Introduce fresh variable for the product
      unsigned bw = product.bitwidth;
      std::size_t fresh_idx =
        get_var_index("__fresh_mul_" + std::to_string(next_fresh++));
      polynomialt fresh_var{bw, mp_integer{1}, fresh_idx};
      side_equations.push_back(fresh_var - product);
      result = fresh_var;
    }
    return result;
  }

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

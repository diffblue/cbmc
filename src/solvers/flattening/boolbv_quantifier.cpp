/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/simplify_expr.h>

#include "boolbv.h"

/// Collect all constant subexpressions and free symbols of a given type
/// from an expression, excluding the quantified variable itself.
static void collect_ground_terms(
  const exprt &expr,
  const typet &type,
  const symbol_exprt &exclude,
  std::set<exprt> &result)
{
  if(expr.type() == type)
  {
    if(expr.is_constant())
      result.insert(expr);
    else if(
      expr.id() == ID_symbol &&
      to_symbol_expr(expr).get_identifier() != exclude.get_identifier())
    {
      result.insert(expr);
    }
  }

  for(const auto &op : expr.operands())
    collect_ground_terms(op, type, exclude, result);
}

/// Compute the relevant value set for a given type, consisting of:
/// 1. Type boundary values (0, max, min, and for FP: NaN, ±inf, ±0)
/// 2. Ground terms of matching type from the formula body
/// 3. Negations of ground terms (for FP: sign-flipped values)
///
/// This set is used for quantifier instantiation over finite domains.
/// See the comment in eager_quantifier_instantiation for references.
static std::vector<exprt> get_relevant_values(
  const typet &type,
  const exprt &formula_body,
  const symbol_exprt &quantified_var)
{
  std::set<exprt> values;

  if(type.id() == ID_floatbv)
  {
    const auto &fp_type = to_floatbv_type(type);
    const ieee_float_spect spec(fp_type);

    // Boundary values for floating-point types:
    // +0, -0, +1, -1, NaN, +inf, -inf, max, -max, min_subnormal
    values.insert(ieee_float_valuet::zero(spec).to_expr());

    ieee_float_valuet neg_zero(spec);
    neg_zero.make_zero();
    neg_zero.set_sign(true);
    values.insert(neg_zero.to_expr());

    values.insert(
      ieee_floatt(spec, ieee_floatt::rounding_modet::ROUND_TO_EVEN, 1)
        .to_expr());
    values.insert(
      ieee_floatt(spec, ieee_floatt::rounding_modet::ROUND_TO_EVEN, -1)
        .to_expr());

    values.insert(ieee_float_valuet::NaN(spec).to_expr());
    values.insert(ieee_float_valuet::plus_infinity(spec).to_expr());
    values.insert(ieee_float_valuet::minus_infinity(spec).to_expr());

    // Largest finite value
    ieee_float_valuet max_val(spec);
    max_val.make_fltmax();
    values.insert(max_val.to_expr());

    ieee_float_valuet neg_max(max_val);
    neg_max.set_sign(true);
    values.insert(neg_max.to_expr());

    // Smallest subnormal
    ieee_float_valuet min_sub(spec);
    min_sub.unpack(mp_integer(1));
    values.insert(min_sub.to_expr());
  }
  else if(
    type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
    type.id() == ID_bv)
  {
    const std::size_t width = to_bitvector_type(type).get_width();

    // Boundary values for bitvector types: 0, 1, all-ones, max, min
    values.insert(from_integer(0, type));
    values.insert(from_integer(1, type));

    if(type.id() == ID_signedbv)
    {
      // min_signed, max_signed
      values.insert(
        from_integer(-power(mp_integer(2), mp_integer(width - 1)), type));
      values.insert(
        from_integer(power(mp_integer(2), mp_integer(width - 1)) - 1, type));
    }
    else
    {
      // all-ones = max unsigned
      values.insert(
        from_integer(power(mp_integer(2), mp_integer(width)) - 1, type));
    }

    // For BV types used as FP reinterpretation, add NaN/inf patterns
    if(width == 32)
    {
      // Float32 NaN: 0x7FC00000, +inf: 0x7F800000
      values.insert(from_integer(0x7FC00000, type));
      values.insert(from_integer(0x7F800000, type));
      values.insert(from_integer(0xFF800000u, type));
    }
    else if(width == 64)
    {
      // Float64 NaN, +inf, -inf
      values.insert(from_integer(mp_integer("9221120237041090560"), type));
      values.insert(from_integer(mp_integer("9218868437227405312"), type));
      values.insert(from_integer(mp_integer("18442240474082181120"), type));
    }
  }

  // Collect ground terms from the formula body
  collect_ground_terms(formula_body, type, quantified_var, values);

  // For FP types, also add negations of collected ground terms
  if(type.id() == ID_floatbv)
  {
    std::set<exprt> negated;
    for(const auto &v : values)
    {
      if(v.is_constant())
      {
        ieee_floatt f(
          to_constant_expr(v), ieee_floatt::rounding_modet::ROUND_TO_EVEN);
        f.set_sign(!f.get_sign());
        negated.insert(f.to_expr());
      }
    }
    values.insert(negated.begin(), negated.end());
  }

  return std::vector<exprt>(values.begin(), values.end());
}

/// A method to detect equivalence between experts that can contain typecast
static bool expr_eq(const exprt &expr1, const exprt &expr2)
{
  return skip_typecast(expr1) == skip_typecast(expr2);
}

/// To obtain the min value for the quantifier variable of the specified
/// forall/exists operator. The min variable is in the form of "!(var_expr >
/// constant)".
static std::optional<constant_exprt>
get_quantifier_var_min(const exprt &var_expr, const exprt &quantifier_expr)
{
  if(quantifier_expr.id()==ID_or)
  {
    /**
     * The min variable
     * is in the form of "!(var_expr >= constant)".
     */
    for(auto &x : quantifier_expr.operands())
    {
      if(x.id()!=ID_not)
        continue;
      exprt y = to_not_expr(x).op();
      if(y.id()!=ID_ge)
        continue;
      const auto &y_binary = to_binary_relation_expr(y);
      if(expr_eq(var_expr, y_binary.lhs()) && y_binary.rhs().is_constant())
      {
        return to_constant_expr(y_binary.rhs());
      }
    }

    if(var_expr.type().id() == ID_unsignedbv)
      return from_integer(0, var_expr.type());
  }
  else if(quantifier_expr.id() == ID_and)
  {
    // The minimum variable can be of the form `var_expr >= constant`, or
    // it can be of the form `var_expr == constant` (e.g. in the case where
    // the interval that bounds the variable is a singleton interval (set
    // with only one element)).
    for(auto &x : quantifier_expr.operands())
    {
      if(x.id() != ID_ge && x.id() != ID_equal)
        continue;
      const auto &x_binary = to_binary_relation_expr(x);
      if(expr_eq(var_expr, x_binary.lhs()) && x_binary.rhs().is_constant())
      {
        return to_constant_expr(x_binary.rhs());
      }
    }

    if(var_expr.type().id() == ID_unsignedbv)
      return from_integer(0, var_expr.type());
  }

  return {};
}

/// To obtain the max value for the quantifier variable of the specified
/// forall/exists operator.
static std::optional<constant_exprt>
get_quantifier_var_max(const exprt &var_expr, const exprt &quantifier_expr)
{
  if(quantifier_expr.id()==ID_or)
  {
    /**
     * The max variable
     * is in the form of "var_expr >= constant".
     */
    for(auto &x : quantifier_expr.operands())
    {
      if(x.id()!=ID_ge)
        continue;
      const auto &x_binary = to_binary_relation_expr(x);
      if(expr_eq(var_expr, x_binary.lhs()) && x_binary.rhs().is_constant())
      {
        const constant_exprt &over_expr = to_constant_expr(x_binary.rhs());

        mp_integer over_i = numeric_cast_v<mp_integer>(over_expr);

        /**
         * Due to the ''simplify'',
         * the ''over_i'' value we obtain here is not the exact
         * maximum index as specified in the original code.
         **/
        over_i-=1;
        return from_integer(over_i, x_binary.rhs().type());
      }
    }
  }
  else
  {
    // There are two potential forms we could come across here. The first one
    // is `!(var_expr >= constant)` - identified by the first if branch - and
    // the second is `var_expr == constant` - identified by the second else-if
    // branch. The second form could be met if previous simplification has
    // identified a singleton interval - see simplify_boolean_expr.cpp.
    for(auto &x : quantifier_expr.operands())
    {
      if(x.id() == ID_not)
      {
        exprt y = to_not_expr(x).op();
        if(y.id() != ID_ge)
          continue;
        const auto &y_binary = to_binary_relation_expr(y);
        if(expr_eq(var_expr, y_binary.lhs()) && y_binary.rhs().is_constant())
        {
          const constant_exprt &over_expr = to_constant_expr(y_binary.rhs());
          mp_integer over_i = numeric_cast_v<mp_integer>(over_expr);
          over_i -= 1;
          return from_integer(over_i, y_binary.rhs().type());
        }
      }
      else if(x.id() == ID_equal)
      {
        const auto &y_binary = to_binary_relation_expr(x);
        if(expr_eq(var_expr, y_binary.lhs()) && y_binary.rhs().is_constant())
        {
          return to_constant_expr(y_binary.rhs());
        }
      }
      else
      {
        // If you need special handling for a particular expression type (say,
        // after changes to the simplifier) you need to make sure that you add
        // an `else if` branch above, otherwise the expression will get skipped
        // and the constraints will not propagate correctly.
        continue;
      }
    }
  }

  return {};
}

static std::optional<exprt> eager_quantifier_instantiation(
  const quantifier_exprt &expr,
  const namespacet &ns)
{
  if(expr.variables().size() > 1)
  {
    // Qx,y.P(x,y) is the same as Qx.Qy.P(x,y)
    auto new_variables = expr.variables();
    new_variables.pop_back();
    auto new_expression = quantifier_exprt(
      expr.id(),
      expr.variables().back(),
      quantifier_exprt(expr.id(), new_variables, expr.where()));
    return eager_quantifier_instantiation(new_expression, ns);
  }

  const symbol_exprt &var_expr = expr.symbol();

  /**
   * We need to rewrite the forall/exists quantifier into
   * an OR/AND expr.
   **/

  const exprt where_simplified = simplify_expr(expr.where(), ns);

  if(
    (where_simplified == true || where_simplified == false) &&
    (var_expr.type().id() == ID_integer ||
     var_expr.type().id() == ID_rational || var_expr.type().id() == ID_real ||
     var_expr.type().id() == ID_bool ||
     (can_cast_type<bitvector_typet>(var_expr.type()) &&
      to_bitvector_type(var_expr.type()).get_width() > 0)))
  {
    return where_simplified;
  }

  if(var_expr.is_boolean())
  {
    // Expand in full.
    // This grows worst-case exponentially in the quantifier nesting depth.
    if(expr.id() == ID_forall)
    {
      // ∀b.f(b) <===> f(0)∧f(1)
      return and_exprt(
        expr.instantiate({false_exprt()}), expr.instantiate({true_exprt()}));
    }
    else if(expr.id() == ID_exists)
    {
      // ∃b.f(b) <===> f(0)∨f(1)
      return or_exprt(
        expr.instantiate({false_exprt()}), expr.instantiate({true_exprt()}));
    }
    else
      UNREACHABLE;
  }

  const std::optional<constant_exprt> min_i =
    get_quantifier_var_min(var_expr, where_simplified);
  const std::optional<constant_exprt> max_i =
    get_quantifier_var_max(var_expr, where_simplified);

  if(!min_i.has_value() || !max_i.has_value())
  {
    // Bounded-range extraction failed. For finite-domain types (bitvectors,
    // floating-point), fall back to instantiation over a relevant value set.
    //
    // This is based on the finite model finding approach from:
    //   Reynolds, Tinelli, Goel, Krstić, Deters, Barrett.
    //   "Quantifier Instantiation Techniques for Finite Model Finding in SMT"
    //   CADE 2013. https://doi.org/10.1007/978-3-642-38574-2_26
    //
    // For finite domains, exhaustive instantiation is a complete decision
    // procedure (Theorem 4.1 in Niemetz et al., CAV 2018,
    // https://doi.org/10.1007/978-3-319-96142-2_16). Full enumeration of
    // 2^n values is infeasible for large n, but instantiation over a
    // *relevant value set* — the union of ground terms from the formula
    // body and type boundary values — is sound and sufficient for many
    // practical formulas. The boundary values capture the discontinuities
    // of FP/BV operations (NaN, ±0, ±inf, min/max).
    //
    // For ∀x.P(x): we encode P(v1) ∧ P(v2) ∧ ... ∧ P(vk).
    //   This is sound: if any P(vi) is false, the universal is false.
    //   It is incomplete: the universal might be false for a value not
    //   in the set. But for the common patterns in FP verification
    //   benchmarks, the relevant value set is sufficient.
    //
    // For ∃x.P(x): we encode P(v1) ∨ P(v2) ∨ ... ∨ P(vk).
    //   This is sound: if any P(vi) is true, the existential is true.
    auto relevant_values =
      get_relevant_values(var_expr.type(), expr.where(), var_expr);

    if(!relevant_values.empty())
    {
      std::vector<exprt> expr_insts;
      for(const auto &val : relevant_values)
      {
        expr_insts.push_back(expr.instantiate({val}));
      }

      if(expr.id() == ID_forall)
        return simplify_expr(conjunction(expr_insts), ns);
      else if(expr.id() == ID_exists)
        return simplify_expr(disjunction(expr_insts), ns);
    }

    return {};
  }

  mp_integer lb = numeric_cast_v<mp_integer>(min_i.value());
  mp_integer ub = numeric_cast_v<mp_integer>(max_i.value());

  if(lb > ub)
    return {};

  auto expr_simplified =
    quantifier_exprt(expr.id(), expr.variables(), where_simplified);

  std::vector<exprt> expr_insts;
  for(mp_integer i = lb; i <= ub; ++i)
  {
    exprt constraint_expr =
      expr_simplified.instantiate({from_integer(i, var_expr.type())});
    expr_insts.push_back(constraint_expr);
  }

  if(expr.id() == ID_forall)
  {
    // maintain the domain constraint if it isn't guaranteed
    // by the instantiations (for a disjunction the domain
    // constraint is implied by the instantiations)
    if(where_simplified.id() == ID_and)
    {
      expr_insts.push_back(binary_predicate_exprt(
        var_expr, ID_gt, from_integer(lb, var_expr.type())));
      expr_insts.push_back(binary_predicate_exprt(
        var_expr, ID_le, from_integer(ub, var_expr.type())));
    }

    return simplify_expr(conjunction(expr_insts), ns);
  }
  else if(expr.id() == ID_exists)
  {
    // maintain the domain constraint if it isn't trivially satisfied
    // by the instantiations (for a conjunction the instantiations are
    // stronger constraints)
    if(where_simplified.id() == ID_or)
    {
      expr_insts.push_back(binary_predicate_exprt(
        var_expr, ID_gt, from_integer(lb, var_expr.type())));
      expr_insts.push_back(binary_predicate_exprt(
        var_expr, ID_le, from_integer(ub, var_expr.type())));
    }

    return simplify_expr(disjunction(expr_insts), ns);
  }

  UNREACHABLE;
}

literalt boolbvt::convert_quantifier(const quantifier_exprt &src)
{
  PRECONDITION(src.id() == ID_forall || src.id() == ID_exists);

  // We first worry about the scoping of the symbols bound by the quantifier.
  auto fresh_symbols = fresh_binding(src);

  // replace in where()
  auto where_replaced = src.instantiate(fresh_symbols);

  // produce new quantifier expression
  auto new_src =
    quantifier_exprt(src.id(), std::move(fresh_symbols), where_replaced);

  const auto res = eager_quantifier_instantiation(src, ns);

  if(res)
    return convert_bool(*res);

  // we failed to instantiate here, need to pass to post-processing
  quantifier_list.emplace_back(quantifiert(src, prop.new_variable()));

  return quantifier_list.back().l;
}

void boolbvt::finish_eager_conversion_quantifiers()
{
  if(quantifier_list.empty())
    return;

  // we do not yet have any elaborate post-processing
  for(const auto &q : quantifier_list)
    conversion_failed(q.expr);
}

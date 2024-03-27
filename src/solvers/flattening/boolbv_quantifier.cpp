/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/invariant.h>
#include <util/simplify_expr.h>
#include <util/ssa_expr.h>

#include "boolbv.h"

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

  if(where_simplified.is_true() || where_simplified.is_false())
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
    return {};

  mp_integer lb = numeric_cast_v<mp_integer>(min_i.value());
  mp_integer ub = numeric_cast_v<mp_integer>(max_i.value());

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

/// Eliminate the quantifier in \p q_expr via E-matching in \p context_map.
/// \return Quantifier-free expression, if quantifier elimination was
///   successful, else nullopt.
static std::optional<exprt> finish_one_quantifier(
  const quantifier_exprt &q_expr,
  const std::unordered_map<const exprt, bvt, irep_hash> &context_map)
{
  if(q_expr.variables().size() > 1)
  {
    // Rewrite Qx,y.P(x,y) as Qy.Qx.P(x,y), just like
    // eager_quantifier_instantiation does.
    auto new_variables = q_expr.variables();
    new_variables.pop_back();
    quantifier_exprt new_expression{
      q_expr.id(),
      q_expr.variables().back(),
      quantifier_exprt{q_expr.id(), new_variables, q_expr.where()}};
    return finish_one_quantifier(new_expression, context_map);
  }

  // find the contexts in which the bound variable is used
  const irep_idt &bound_variable_id = q_expr.symbol().get_identifier();
  bool required_context = false;
  std::unordered_set<index_exprt, irep_hash> index_contexts;
  auto context_finder =
    [&bound_variable_id, &required_context, &index_contexts](const exprt &e) {
      if(auto symbol_expr = expr_try_dynamic_cast<symbol_exprt>(e))
      {
        required_context |= bound_variable_id == symbol_expr->get_identifier();
      }
      else if(required_context)
      {
        if(auto index_expr = expr_try_dynamic_cast<index_exprt>(e))
        {
          index_contexts.insert(*index_expr);
          required_context = false;
        }
      }
    };
  q_expr.where().visit_post(context_finder);
  // make sure we found some context for instantiation
  if(index_contexts.empty())
    return {};

  // match the contexts against expressions that we have cached
  std::unordered_set<exprt, irep_hash> instantiation_candidates;
  for(const auto &cache_entry : context_map)
  {
    // consider re-organizing the cache to use expression ids at the top level
    if(auto index_expr = expr_try_dynamic_cast<index_exprt>(cache_entry.first))
    {
      for(const auto &index_context : index_contexts)
      {
        if(
          auto ssa_context =
            expr_try_dynamic_cast<ssa_exprt>(index_context.array()))
        {
          if(
            auto ssa_array =
              expr_try_dynamic_cast<ssa_exprt>(index_expr->array()))
          {
            if(
              ssa_context->get_l1_object_identifier() ==
              ssa_array->get_l1_object_identifier())
            {
              instantiation_candidates.insert(index_expr->index());
              break;
            }
          }
        }
        else if(index_expr->array() == index_context.array())
        {
          instantiation_candidates.insert(index_expr->index());
          break;
        }
      }
    }
  }

  if(instantiation_candidates.empty())
    return {};

  exprt::operandst instantiations;
  instantiations.reserve(instantiation_candidates.size());
  for(const auto &e : instantiation_candidates)
  {
    exprt::operandst values{
      {typecast_exprt::conditional_cast(e, q_expr.symbol().type())}};
    instantiations.push_back(q_expr.instantiate(values));
  }

  if(q_expr.id() == ID_exists)
    return disjunction(instantiations);
  else
    return conjunction(instantiations);
}

void boolbvt::finish_eager_conversion_quantifiers()
{
  for(const auto &q : quantifier_list)
  {
    auto result_opt =
      finish_one_quantifier(to_quantifier_expr(q.expr), bv_cache);
    if(!result_opt.has_value())
    {
      conversion_failed(q.expr);
      continue;
    }

    // Nested quantifiers may yield additional entries in quantifier_list via
    // convert; the range-for remains safe to use as long as quantifier_list is
    // a std::list.
    literalt result_lit = convert(*result_opt);
    prop.l_set_to_true(prop.lequal(q.l, result_lit));
  }
}

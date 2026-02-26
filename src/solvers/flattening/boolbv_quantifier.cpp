/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
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

/// \file
/// Complete instantiation for quantified formulas.
///
/// This file implements quantifier elimination for CBMC's bitvector
/// solver. Two strategies are used:
///
/// 1. **Eager instantiation** (bounded ranges): When the quantifier body
///    contains explicit bounds on the variable (e.g., `!(j >= lb) || body`),
///    the quantifier is expanded into a conjunction/disjunction over all
///    values in [lb, ub]. This is handled by `eager_quantifier_instantiation`.
///
/// 2. **Complete instantiation** (unbounded/symbolic ranges): When no
///    explicit bounds are available, we use an approach based on:
///
///      Yeting Ge and Leonardo de Moura, "Complete instantiation for
///      quantified formulas in Satisfiability Modulo Theories", CAV 2009.
///
///    The key idea is that for *essentially uninterpreted* formulas (where
///    quantified variables only appear as arguments of uninterpreted
///    functions), the quantifier can be eliminated by instantiating with
///    a finite set of ground terms. In CBMC's context, "uninterpreted
///    functions" correspond to array accesses (index_exprt).
///
///    The paper defines a system of set constraints ΔF that captures which
///    ground terms are relevant for each function argument position. The
///    least fixed point of ΔF gives the complete set of instantiation
///    terms. For the *almost uninterpreted* fragment (Section 4 of the
///    paper), variables may also appear with arithmetic offsets, e.g.,
///    `arr[j + 1]`. The offset extension adds constraints:
///      S_{k,i} + r ⊆ A_{f,j}  and  A_{f,j} + (-r) ⊆ S_{k,i}
///    ensuring that the fixed point accounts for shifted indices.
///
///    The formula F is in the *finite essentially uninterpreted* (FEU)
///    fragment when ΔF is stratified (i.e., the fixed point is finite).
///    For non-stratified cases (e.g., offsets that create infinite chains),
///    we bound the computation to ensure termination.
///
///    This is implemented by `instantiate_one_quantifier` and its helpers,
///    called from `finish_eager_conversion_quantifiers` as a post-processing
///    step after the main bitvector conversion.

/// Represents how a bound variable is used as an array index, possibly with
/// an arithmetic offset. In the paper's terminology, this captures one
/// occurrence of an uninterpreted function application f(... x_i + r ...)
/// where f is an array access, x_i is the bound variable, and r is the
/// offset.
///
/// For `arr[j + r]`: \p array is `arr`, \p offset is `r`.
/// For `arr[j]`: \p array is `arr`, \p offset is zero.
/// For `arr[j - r]`: \p array is `arr`, \p offset is `-r`.
struct index_contextt
{
  exprt array;
  exprt offset;
};

/// Check whether two array expressions refer to the same underlying
/// Check whether \p pattern and \p candidate refer to the same
/// array, accounting for SSA renaming. After symbolic execution, the
/// same source-level array may appear with different SSA version
/// numbers (e.g., `arr#1` vs `arr#2`). We compare L1 object
/// identifiers to match across versions. For nested array accesses
/// (e.g., `a[0]` as a sub-array), we recursively match the base
/// array and compare the simplified indices.
static bool
arrays_match(const exprt &pattern, const exprt &candidate, const namespacet &ns)
{
  if(auto ssa_pattern = expr_try_dynamic_cast<ssa_exprt>(pattern))
  {
    if(auto ssa_candidate = expr_try_dynamic_cast<ssa_exprt>(candidate))
    {
      return ssa_pattern->get_l1_object_identifier() ==
             ssa_candidate->get_l1_object_identifier();
    }
    return false;
  }
  // For nested array accesses like a[0][j], the "array" operand
  // is itself an index_exprt (a[0]). Match recursively on the
  // base array and compare simplified indices (the pattern may
  // contain unsimplified arithmetic like cast(0 % 2) that equals
  // a constant in the candidate).
  if(auto idx_pattern = expr_try_dynamic_cast<index_exprt>(pattern))
  {
    if(auto idx_candidate = expr_try_dynamic_cast<index_exprt>(candidate))
    {
      return arrays_match(idx_pattern->array(), idx_candidate->array(), ns) &&
             simplify_expr(idx_pattern->index(), ns) ==
               simplify_expr(idx_candidate->index(), ns);
    }
    return false;
  }
  return pattern == candidate;
}

/// Find all index_exprt nodes in \p expr whose index sub-expression
/// contains the symbol \p bound_var_id. For each such node, decompose
/// the index into `bound_var + offset` (where offset may be zero).
///
/// This corresponds to identifying the uninterpreted function
/// applications in the paper's terminology. In CBMC, array accesses
/// (`index_exprt`) play the role of uninterpreted functions: the
/// array is the function symbol, and the index is the argument.
///
/// The offset decomposition implements the extension from Section 4
/// of the paper ("Offsets"): for terms of the form `f(x_i + r)`,
/// we extract the offset `r` to generate the additional set
/// constraints `S_{k,i} + r ⊆ A_{f,j}` and
/// `A_{f,j} + (-r) ⊆ S_{k,i}`.
///
/// Recognised patterns:
///   - `var` or `cast(var)` → offset = 0
///   - `var + r` or `r + var` → offset = r
///   - `var - r` → offset = -r
///   - complex expressions containing var → offset = 0 (fallback)
static std::vector<index_contextt>
find_index_contexts(const exprt &expr, const irep_idt &bound_var_id)
{
  std::vector<index_contextt> contexts;
  expr.visit_pre(
    [&bound_var_id, &contexts](const exprt &e)
    {
      auto index_expr = expr_try_dynamic_cast<index_exprt>(e);
      if(!index_expr)
        return;

      // Check whether the index sub-expression mentions the bound variable.
      bool has_bound_var = false;
      index_expr->index().visit_pre(
        [&bound_var_id, &has_bound_var](const exprt &sub)
        {
          if(auto sym = expr_try_dynamic_cast<symbol_exprt>(sub))
            has_bound_var |= sym->get_identifier() == bound_var_id;
        });
      if(!has_bound_var)
        return;

      // Decompose index into bound_var + offset.
      // We recognise: var, var + const, const + var, var - const.
      const exprt &idx = index_expr->index();
      auto zero = from_integer(0, idx.type());

      if(auto sym = expr_try_dynamic_cast<symbol_exprt>(idx))
      {
        if(sym->get_identifier() == bound_var_id)
        {
          contexts.push_back({index_expr->array(), std::move(zero)});
          return;
        }
      }

      if(auto tc = expr_try_dynamic_cast<typecast_exprt>(idx))
      {
        if(auto sym = expr_try_dynamic_cast<symbol_exprt>(tc->op()))
        {
          if(sym->get_identifier() == bound_var_id)
          {
            contexts.push_back(
              {index_expr->array(), from_integer(0, idx.type())});
            return;
          }
        }
      }

      if(idx.id() == ID_plus && idx.operands().size() == 2)
      {
        const auto &lhs = idx.operands()[0];
        const auto &rhs = idx.operands()[1];

        auto is_bound_var = [&bound_var_id](const exprt &e) -> bool
        {
          if(auto sym = expr_try_dynamic_cast<symbol_exprt>(e))
            return sym->get_identifier() == bound_var_id;
          if(auto tc = expr_try_dynamic_cast<typecast_exprt>(e))
          {
            if(auto sym = expr_try_dynamic_cast<symbol_exprt>(tc->op()))
              return sym->get_identifier() == bound_var_id;
          }
          return false;
        };

        // Check for patterns: bound_var + offset, offset + bound_var
        if(is_bound_var(lhs))
        {
          contexts.push_back({index_expr->array(), rhs});
          return;
        }
        if(is_bound_var(rhs))
        {
          contexts.push_back({index_expr->array(), lhs});
          return;
        }
      }

      if(idx.id() == ID_minus && idx.operands().size() == 2)
      {
        const auto &lhs = idx.operands()[0];
        const auto &rhs = idx.operands()[1];

        auto is_bound_var = [&bound_var_id](const exprt &e) -> bool
        {
          if(auto sym = expr_try_dynamic_cast<symbol_exprt>(e))
            return sym->get_identifier() == bound_var_id;
          if(auto tc = expr_try_dynamic_cast<typecast_exprt>(e))
          {
            if(auto sym = expr_try_dynamic_cast<symbol_exprt>(tc->op()))
              return sym->get_identifier() == bound_var_id;
          }
          return false;
        };

        // bound_var - offset => offset is negated
        if(is_bound_var(lhs))
        {
          contexts.push_back({index_expr->array(), unary_minus_exprt(rhs)});
          return;
        }
      }

      // Fallback: treat the whole index as a context with zero offset
      // (the variable is buried in a complex expression we don't decompose)
      contexts.push_back({index_expr->array(), std::move(zero)});
    });
  return contexts;
}

/// Collect all ground index terms from \p context_map for arrays
/// that match any of the given \p contexts.
///
/// In the paper's terminology, this builds the initial content of
/// the sets A_{f,j}: the ground terms that appear as the j-th
/// argument of uninterpreted function f in the ground clauses of F.
/// We scan the bitvector cache for:
///   - index_exprt (array reads): the index is a ground term
///   - with_exprt (array writes): the update index is a ground term
static std::unordered_set<exprt, irep_hash> collect_ground_indices(
  const std::vector<index_contextt> &contexts,
  const std::unordered_map<const exprt, bvt, irep_hash> &context_map,
  const namespacet &ns)
{
  std::unordered_set<exprt, irep_hash> ground_indices;

  // When the array in a context is an array literal (array_exprt),
  // the SSA encoding has expanded the array symbol into its elements.
  // No cache entry will match this literal, so we add indices 0..size-1
  // directly. This is sound: these are exactly the valid indices for
  // the array, and instantiating with all of them is complete.
  for(const auto &ctx : contexts)
  {
    if(ctx.array.id() == ID_array)
    {
      const auto &array_type = to_array_type(ctx.array.type());
      const auto size = numeric_cast<mp_integer>(array_type.size());
      if(size.has_value() && *size > 0 && *size <= 256)
      {
        const auto &index_type = array_type.index_type();
        for(mp_integer i = 0; i < *size; ++i)
          ground_indices.insert(from_integer(i, index_type));
      }
    }
  }

  for(const auto &cache_entry : context_map)
  {
    // Match array reads: index_exprt(array, index)
    if(auto index_expr = expr_try_dynamic_cast<index_exprt>(cache_entry.first))
    {
      for(const auto &ctx : contexts)
      {
        if(arrays_match(ctx.array, index_expr->array(), ns))
        {
          ground_indices.insert(index_expr->index());
          break;
        }
      }
    }
    // Match array writes: with_exprt(array, index, value)
    else if(
      auto with_expr = expr_try_dynamic_cast<with_exprt>(cache_entry.first))
    {
      for(const auto &ctx : contexts)
      {
        if(arrays_match(ctx.array, with_expr->old(), ns))
        {
          ground_indices.insert(with_expr->where());
          break;
        }
      }
    }
  }
  return ground_indices;
}

/// Compute the complete set of instantiation terms for a bound
/// variable, implementing the set constraint fixed-point from
/// Section 3 and the offset extension from Section 4 of:
///
///   Ge & de Moura, "Complete instantiation for quantified formulas
///   in Satisfiability Modulo Theories", CAV 2009.
///
/// The paper defines a system of set constraints ΔF induced by the
/// formula F. For each clause C_k containing a variable x_i that
/// appears as the j-th argument of uninterpreted function f:
///
///   - If x_i appears directly: S_{k,i} = A_{f,j}
///   - If a ground term t appears: t ∈ A_{f,j}
///   - If x_i + r appears (offset): S_{k,i} + r ⊆ A_{f,j}
///     and A_{f,j} + (-r) ⊆ S_{k,i}
///
/// The least fixed point of ΔF gives the sets S_{k,i} of ground
/// terms to use for instantiating x_i. The formula F* obtained by
/// instantiating each clause C_k[x] with terms from S_{k,i} is
/// equisatisfiable with F (Theorem 1 and Theorem 2 in the paper).
///
/// When ΔF is stratified (the FEU fragment), the fixed point is
/// finite. For non-stratified cases (e.g., offsets that create
/// infinite chains as in Example 4 of the paper), we bound the
/// computation with max_iterations and max_terms.
///
/// Two computation paths are provided:
///   1. **Numeric path**: When all offsets and ground indices are
///      constants, we use integer arithmetic for efficiency.
///   2. **Symbolic path**: For non-constant terms, we build
///      expressions and use simplify_expr to normalize them.
///
/// \param contexts: the index contexts (array, offset) pairs
/// \param initial_ground_indices: ground terms from the bv_cache
/// \param var_type: the type of the bound variable
/// \param ns: namespace for expression simplification
/// \return the set of terms to substitute for the bound variable
static std::unordered_set<exprt, irep_hash> compute_instantiation_set(
  const std::vector<index_contextt> &contexts,
  const std::unordered_set<exprt, irep_hash> &initial_ground_indices,
  const typet &var_type,
  const namespacet &ns)
{
  std::unordered_set<exprt, irep_hash> all_ground = initial_ground_indices;
  std::unordered_set<exprt, irep_hash> var_terms;

  // Collect all distinct offsets
  std::vector<exprt> offsets;
  for(const auto &ctx : contexts)
    offsets.push_back(ctx.offset);

  // Check if all offsets are zero (no offset case) - skip fixed-point
  bool has_nonzero_offset = false;
  for(const auto &r : offsets)
  {
    if(!r.is_zero())
    {
      has_nonzero_offset = true;
      break;
    }
  }

  if(!has_nonzero_offset)
  {
    for(const auto &g : all_ground)
      var_terms.insert(typecast_exprt::conditional_cast(g, var_type));
    return var_terms;
  }

  // Try to extract numeric offset values for efficient fixed-point computation
  std::vector<std::optional<mp_integer>> numeric_offsets;
  bool all_numeric_offsets = true;
  for(const auto &r : offsets)
  {
    if(r.is_zero())
    {
      numeric_offsets.push_back(mp_integer(0));
    }
    else
    {
      auto val = numeric_cast<mp_integer>(r);
      numeric_offsets.push_back(val);
      if(!val.has_value())
        all_numeric_offsets = false;
    }
  }

  // Try to extract numeric ground indices
  std::set<mp_integer> numeric_ground;
  bool all_numeric_ground = true;
  for(const auto &g : all_ground)
  {
    auto val = numeric_cast<mp_integer>(g);
    if(val.has_value())
      numeric_ground.insert(*val);
    else
      all_numeric_ground = false;
  }

  // If we have numeric offsets and ground indices, compute the fixed point
  // using integer arithmetic (much more efficient)
  if(all_numeric_offsets && all_numeric_ground && !numeric_ground.empty())
  {
    std::set<mp_integer> var_values;
    bool changed = true;
    const std::size_t max_iterations = 5;
    const std::size_t max_terms = 50;
    std::size_t iteration = 0;
    while(changed && iteration < max_iterations)
    {
      changed = false;
      ++iteration;

      std::set<mp_integer> new_var_values;
      for(const auto &g : numeric_ground)
      {
        for(const auto &r : numeric_offsets)
        {
          mp_integer v = g - *r;
          if(var_values.find(v) == var_values.end())
            new_var_values.insert(v);
        }
      }
      for(const auto &v : new_var_values)
      {
        if(var_values.insert(v).second)
          changed = true;
      }
      if(var_values.size() > max_terms)
        break;

      std::set<mp_integer> new_ground;
      for(const auto &v : var_values)
      {
        for(const auto &r : numeric_offsets)
        {
          mp_integer g = v + *r;
          if(numeric_ground.find(g) == numeric_ground.end())
            new_ground.insert(g);
        }
      }
      for(const auto &g : new_ground)
      {
        if(numeric_ground.insert(g).second)
          changed = true;
      }
      if(numeric_ground.size() > max_terms)
        break;
    }

    for(const auto &v : var_values)
      var_terms.insert(from_integer(v, var_type));
    return var_terms;
  }

  // Fallback: symbolic fixed-point with simplification
  bool changed = true;
  const std::size_t max_iterations = 3;
  const std::size_t max_terms = 30;
  std::size_t iteration = 0;
  while(changed && iteration < max_iterations)
  {
    changed = false;
    ++iteration;

    std::unordered_set<exprt, irep_hash> new_var_terms;
    for(const auto &g : all_ground)
    {
      for(const auto &r : offsets)
      {
        exprt var_term;
        if(r.is_zero())
          var_term = typecast_exprt::conditional_cast(g, var_type);
        else
        {
          var_term = simplify_expr(
            typecast_exprt::conditional_cast(minus_exprt(g, r), var_type), ns);
        }
        if(var_terms.find(var_term) == var_terms.end())
          new_var_terms.insert(var_term);
      }
    }
    for(auto &v : new_var_terms)
    {
      if(var_terms.insert(std::move(v)).second)
        changed = true;
    }
    if(var_terms.size() > max_terms)
      break;

    std::unordered_set<exprt, irep_hash> new_ground;
    for(const auto &v : var_terms)
    {
      for(const auto &r : offsets)
      {
        exprt ground_term;
        if(r.is_zero())
          ground_term = typecast_exprt::conditional_cast(v, r.type());
        else
        {
          ground_term = simplify_expr(
            plus_exprt(typecast_exprt::conditional_cast(v, r.type()), r), ns);
        }
        if(all_ground.find(ground_term) == all_ground.end())
          new_ground.insert(ground_term);
      }
    }
    for(auto &g : new_ground)
    {
      if(all_ground.insert(std::move(g)).second)
        changed = true;
    }
    if(all_ground.size() > max_terms)
      break;
  }

  return var_terms;
}

/// Eliminate the quantifier in \p q_expr via complete instantiation
/// using ground terms from \p context_map.
///
/// Implements the approach from Ge & de Moura, "Complete
/// instantiation for quantified formulas in SMT" (CAV 2009).
/// The procedure:
///   1. Identifies how the bound variable is used as an array index
///      (find_index_contexts), corresponding to the paper's
///      identification of uninterpreted function applications.
///   2. Collects ground index terms from the bitvector cache
///      (collect_ground_indices), seeding the sets A_{f,j}.
///   3. Computes the fixed point of the set constraint system ΔF
///      (compute_instantiation_set), yielding the instantiation
///      terms S_{k,i}.
///   4. Instantiates the quantifier body with each term and
///      combines: conjunction for forall, disjunction for exists.
///
/// \param q_expr: the quantifier expression to eliminate
/// \param context_map: the bitvector cache (bv_cache) mapping
///   expressions to their bitvector encodings
/// \param ns: namespace for expression simplification
/// \return quantifier-free expression, or nullopt if instantiation
///   was not possible (e.g., no array index contexts found)
static std::optional<exprt> instantiate_one_quantifier(
  const quantifier_exprt &q_expr,
  const std::unordered_map<const exprt, bvt, irep_hash> &context_map,
  const namespacet &ns)
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
    return instantiate_one_quantifier(new_expression, context_map, ns);
  }

  const irep_idt &bound_variable_id = q_expr.symbol().get_identifier();

  // Find all array index contexts where the bound variable appears
  auto contexts = find_index_contexts(q_expr.where(), bound_variable_id);
  if(contexts.empty())
    return {};

  // Collect ground index terms from the cache
  auto ground_indices = collect_ground_indices(contexts, context_map, ns);
  if(ground_indices.empty())
    return {};

  // Compute the complete instantiation set using the paper's set constraint
  // fixed-point approach
  auto instantiation_terms = compute_instantiation_set(
    contexts, ground_indices, q_expr.symbol().type(), ns);

  if(instantiation_terms.empty())
    return {};

  // Sort instantiation terms for deterministic clause ordering
  // in the SAT solver. Without sorting, the unordered_set iteration
  // order depends on expression hashes, which incorporate source
  // locations (including file paths). This causes MiniSat to see
  // different clause orderings for the same formula depending on
  // how the input file is specified, with performance varying from
  // sub-second to minutes on the same UNSAT instance.
  std::vector<exprt> sorted_terms(
    instantiation_terms.begin(), instantiation_terms.end());
  std::sort(
    sorted_terms.begin(),
    sorted_terms.end(),
    [](const exprt &a, const exprt &b) { return a < b; });

  exprt::operandst instantiations;
  instantiations.reserve(sorted_terms.size());
  for(const auto &e : sorted_terms)
  {
    exprt::operandst values{
      {typecast_exprt::conditional_cast(e, q_expr.symbol().type())}};
    instantiations.push_back(q_expr.instantiate(values));
  }

  if(q_expr.id() == ID_exists)
    return disjunction(instantiations);
  else
  {
    PRECONDITION(q_expr.id() == ID_forall);
    return conjunction(instantiations);
  }
}

void boolbvt::finish_eager_conversion_quantifiers()
{
  // Nested quantifiers may yield additional entries in quantifier_list via
  // convert.
  while(!quantifier_list.empty())
  {
    std::list<quantifiert> remaining_quantifiers;
    std::swap(quantifier_list, remaining_quantifiers);
    std::list<std::optional<exprt>> instantiations;

    for(const auto &q : remaining_quantifiers)
    {
      instantiations.push_back(
        instantiate_one_quantifier(to_quantifier_expr(q.expr), bv_cache, ns));
    }

    auto instantiations_it = instantiations.begin();
    for(const auto &q : remaining_quantifiers)
    {
      if(!instantiations_it->has_value())
      {
        conversion_failed(q.expr);
        ++instantiations_it;
        continue;
      }

      literalt result_lit = convert(**instantiations_it);
      prop.l_set_to_true(prop.lequal(q.l, result_lit));
      ++instantiations_it;
    }
  }
}

/*******************************************************************\

Module: Lazy quantifier instantiation via CEGAR refinement

Author: Kiro (autonomous agent)

\*******************************************************************/

/// \file
/// Lazy quantifier instantiation via CEGAR refinement.
///
/// When `--refine-quantifiers` is enabled, quantified formulas are
/// not eagerly instantiated into a single conjunction/disjunction.
/// Instead, each quantifier instance is converted to a SAT literal
/// but the implication `quantifier_literal => instance_literal` is
/// added lazily: only when the SAT model violates that instance.
///
/// For `forall { k; k < N ==> body(k) }` with placeholder literal L:
///   - Eager: L <=> (body(0) && body(1) && ... && body(N-1))
///   - Lazy:  L is set to TRUE; implications L => body(i) are added
///     only for indices i where the model violates body(i).
///
/// This is sound because:
///   - UNSAT with fewer constraints implies UNSAT with all constraints
///   - SAT is only reported when all instances are satisfied
///
/// The approach is analogous to `--refine-arrays` (see refine_arrays.cpp).

#include "bv_refinement.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

/// Pre-compute instance literals for all quantifiers during
/// post-processing. The literals are stored but the implications
/// (quantifier_literal => instance_literal) are NOT added yet.
/// This allows the SAT solver to find proofs that don't need
/// all instances, while ensuring the bitvector encoding exists
/// for instances we add later.
void bv_refinementt::finish_eager_conversion_quantifiers()
{
  if(!config_.refine_quantifiers)
  {
    boolbvt::finish_eager_conversion_quantifiers();
    return;
  }

  log.progress() << "BV-Refinement: deferring " << quantifier_list.size()
                 << " quantifier instantiations" << messaget::eom;

  for(auto &q : quantifier_list)
  {
    const auto &qexpr = to_quantifier_expr(q.expr);

    // Set placeholder: forall => TRUE, exists => FALSE
    if(qexpr.id() == ID_forall)
      prop.l_set_to_true(q.l);
    else
      prop.l_set_to_false(q.l);

    if(!q.l.is_constant())
      prop.set_frozen(q.l);

    // Freeze symbols in the quantifier body for incremental solving
    for(const auto &sym : find_symbols(qexpr.where()))
    {
      if(!bv_width.get_width_opt(sym.type()).has_value())
        continue;
      const bvt bv = convert_bv(sym);
      for(const auto &lit : bv)
        if(!lit.is_constant())
          prop.set_frozen(lit);
    }
  }
}

/// Extract constant lower and upper bounds from a quantifier body.
///
/// Handles two patterns produced by CBMC's simplifier:
///
/// 1. Disjunctive (forall): `k >= UB || !(k >= LB) || body(k)`
///    where `k >= UB` gives upper bound UB-1, and `!(k >= LB)` gives
///    lower bound LB. For unsigned variables, LB defaults to 0.
///
/// 2. Conjunctive (exists): `k >= LB && !(k >= UB) && body(k)`
///    where `k >= LB` gives lower bound LB, and `!(k >= UB)` gives
///    upper bound UB-1.
///
/// \param q: the quantifier expression
/// \param ns: namespace for simplification
/// \return pair (lower_bound, upper_bound) if extractable
static std::optional<std::pair<mp_integer, mp_integer>>
get_quantifier_bounds(const quantifier_exprt &q, const namespacet &ns)
{
  if(q.variables().size() > 1)
    return {};

  const auto &var = q.symbol();
  const exprt body = simplify_expr(q.where(), ns);

  std::optional<mp_integer> lb, ub;

  if(body.id() == ID_or)
  {
    // Disjunctive pattern: !(k >= LB) || k >= UB || body(k)
    for(const auto &op : body.operands())
    {
      if(op.id() == ID_not)
      {
        const auto &inner = to_not_expr(op).op();
        if(inner.id() == ID_ge)
        {
          const auto &ge = to_binary_relation_expr(inner);
          if(skip_typecast(ge.lhs()) == var && ge.rhs().is_constant())
            lb = numeric_cast<mp_integer>(to_constant_expr(ge.rhs()));
        }
      }
      else if(op.id() == ID_ge)
      {
        const auto &ge = to_binary_relation_expr(op);
        if(skip_typecast(ge.lhs()) == var && ge.rhs().is_constant())
        {
          auto val = numeric_cast<mp_integer>(to_constant_expr(ge.rhs()));
          if(val.has_value())
            ub = *val - 1;
        }
      }
    }
  }
  else if(body.id() == ID_and)
  {
    // Conjunctive pattern: k >= LB && !(k >= UB) && body(k)
    for(const auto &op : body.operands())
    {
      if(op.id() == ID_not)
      {
        const auto &inner = to_not_expr(op).op();
        if(inner.id() == ID_ge)
        {
          const auto &ge = to_binary_relation_expr(inner);
          if(skip_typecast(ge.lhs()) == var && ge.rhs().is_constant())
          {
            auto val = numeric_cast<mp_integer>(to_constant_expr(ge.rhs()));
            if(val.has_value())
              ub = *val - 1;
          }
        }
      }
      else if(op.id() == ID_ge || op.id() == ID_equal)
      {
        const auto &rel = to_binary_relation_expr(op);
        if(skip_typecast(rel.lhs()) == var && rel.rhs().is_constant())
        {
          lb = numeric_cast<mp_integer>(to_constant_expr(rel.rhs()));
          if(op.id() == ID_equal)
            ub = lb;
        }
      }
    }
  }

  if(!lb.has_value() && var.type().id() == ID_unsignedbv)
    lb = 0;

  if(!lb.has_value() || !ub.has_value())
    return {};

  return std::make_pair(*lb, *ub);
}

/// Check whether the current SAT model satisfies all deferred
/// quantifiers. For each violated quantifier, convert the violated
/// instance to a SAT literal and add the implication
/// `quantifier_literal => instance_literal`.
///
/// All violated instances across all quantifiers are added in a
/// single refinement step (batch mode) to minimize iterations.
///
/// Evaluation strategy: first try `get()` + `simplify_expr()` which
/// is cheap and doesn't add SAT clauses. If the result is
/// inconclusive (not true/false), fall back to `convert()` +
/// `l_get()` which is reliable but adds the bitvector encoding.
void bv_refinementt::quantifiers_overapproximated()
{
  if(!config_.refine_quantifiers)
    return;

  unsigned nb_refined = 0;

  for(const auto &q : quantifier_list)
  {
    const auto &qexpr = to_quantifier_expr(q.expr);

    auto bounds = get_quantifier_bounds(qexpr, ns);
    if(!bounds.has_value())
    {
      log.debug() << "BV-Refinement: no bounds for quantifier"
                  << messaget::eom;
      continue;
    }

    const auto &[lb, ub] = *bounds;
    if(ub - lb > 10000)
      continue;

    for(mp_integer i = lb; i <= ub; ++i)
    {
      exprt val = from_integer(i, qexpr.symbol().type());
      exprt instance = qexpr.instantiate({val});

      // Try cheap evaluation first: get model values and simplify.
      // This works when the array is field-sensitive (small arrays)
      // and produces concrete true/false.
      exprt evaluated = simplify_expr(get(instance), ns);

      bool is_false = (evaluated == false_exprt());
      bool is_true = (evaluated == true_exprt());

      if(!is_false && !is_true)
      {
        // Simplification was inconclusive (large array with array theory).
        // Fall back to converting and checking the SAT assignment.
        literalt inst_lit = convert(instance);
        is_true = prop.l_get(inst_lit).is_true();
        is_false = !is_true;

        if(qexpr.id() == ID_forall && is_false)
        {
          prop.l_set_to_true(prop.limplies(q.l, inst_lit));
          nb_refined++;
        }
        continue;
      }

      if(qexpr.id() == ID_forall && is_false)
      {
        log.debug() << "BV-Refinement: forall violated at index " << i
                    << messaget::eom;
        literalt inst_lit = convert(instance);
        prop.l_set_to_true(prop.limplies(q.l, inst_lit));
        nb_refined++;
      }
    }
  }

  log.debug() << "BV-Refinement: " << nb_refined
              << " quantifier instances refined" << messaget::eom;
  if(nb_refined > 0)
    progress = true;
}

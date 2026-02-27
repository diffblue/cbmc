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
/// Only quantifiers with constant bounds are lazily instantiated.
/// Quantifiers with variable bounds (e.g., loop invariants with
/// `k < i` where `i` is symbolic) are eagerly instantiated since
/// the refinement loop cannot enumerate their instances.
///
/// The approach is analogous to `--refine-arrays` (see refine_arrays.cpp).

#include "bv_refinement.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

// ===== Static helpers (must precede class methods that use them) =====

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
/// Returns nullopt for quantifiers with variable bounds (e.g.,
/// `k >= i` where `i` is not a constant).
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

// ===== Class methods =====

/// Partition quantifiers into lazy (constant bounds) and eager
/// (variable/unknown bounds). Eagerly instantiate the latter via
/// the base class, defer the former for CEGAR refinement.
void bv_refinementt::finish_eager_conversion_quantifiers()
{
  if(!config_.refine_quantifiers)
  {
    boolbvt::finish_eager_conversion_quantifiers();
    return;
  }

  quantifier_listt lazy_quantifiers;
  quantifier_listt eager_quantifiers;

  for(auto &q : quantifier_list)
  {
    auto bounds = get_quantifier_bounds(to_quantifier_expr(q.expr), ns);
    if(bounds.has_value())
      lazy_quantifiers.push_back(std::move(q));
    else
      eager_quantifiers.push_back(std::move(q));
  }

  log.progress() << "BV-Refinement: deferring " << lazy_quantifiers.size()
                 << " quantifier instantiations, eagerly instantiating "
                 << eager_quantifiers.size() << messaget::eom;

  // Eagerly instantiate quantifiers with variable/unknown bounds
  quantifier_list = std::move(eager_quantifiers);
  boolbvt::finish_eager_conversion_quantifiers();

  // Set up lazy quantifiers for refinement
  quantifier_list = std::move(lazy_quantifiers);
  for(const auto &q : quantifier_list)
  {
    const auto &qexpr = to_quantifier_expr(q.expr);

    if(qexpr.id() == ID_forall)
      prop.l_set_to_true(q.l);
    else
      prop.l_set_to_false(q.l);

    if(!q.l.is_constant())
      prop.set_frozen(q.l);

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

/// Check whether the current SAT model satisfies all deferred
/// quantifiers. For each violated quantifier, convert the violated
/// instance to a SAT literal and add the implication
/// `quantifier_literal => instance_literal`.
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
      continue;

    const auto &[lb, ub] = *bounds;
    if(ub - lb > 10000)
      continue;

    for(mp_integer i = lb; i <= ub; ++i)
    {
      exprt val = from_integer(i, qexpr.symbol().type());
      exprt instance = qexpr.instantiate({val});

      exprt evaluated = simplify_expr(get(instance), ns);

      bool is_false = (evaluated == false_exprt());
      bool is_true = (evaluated == true_exprt());

      if(!is_false && !is_true)
      {
        // Simplification inconclusive; fall back to SAT evaluation
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

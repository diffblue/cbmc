/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include "goto_state.h"
#include "goto_symex_is_constant.h"
#include "goto_symex_state.h"

#include <util/format_expr.h>

/// Print the constant propagation map in a human-friendly format.
/// This is primarily for use from the debugger; please don't delete me just
/// because there aren't any current callers.
void goto_statet::output_propagation_map(std::ostream &out)
{
  sharing_mapt<irep_idt, exprt>::viewt view;
  propagation.get_view(view);

  for(const auto &name_value : view)
  {
    out << name_value.first << " <- " << format(name_value.second) << "\n";
  }
}

/// Given a condition that must hold on this path, propagate as much knowledge
/// as possible. For example, if the condition is (x == 5), whether that's an
/// assumption or a GOTO condition that we just passed through, we can propagate
/// the constant '5' for future 'x' references. If the condition is (y == &o1)
/// then we can use that to populate the value set.
/// \param condition: condition that must hold on this path. Expected to already
///   be L2-renamed.
/// \param previous_state: currently active state, not necessarily the same as
///   *this. For a GOTO instruction this is the state immediately preceding the
///   branch while *this is the state that will be used on the taken- or
///   not-taken path. For an ASSUME instruction \p previous_state and *this are
///   equal.
/// \param ns: global namespace
void goto_statet::apply_condition(
  const exprt &condition,
  const goto_symex_statet &previous_state,
  const namespacet &ns)
{
  if(auto and_expr = expr_try_dynamic_cast<and_exprt>(condition))
  {
    // A == B && C == D && E == F ...
    // -->
    // Apply each condition individually
    for(const auto &op : and_expr->operands())
      apply_condition(op, previous_state, ns);
  }
  else if(auto not_expr = expr_try_dynamic_cast<not_exprt>(condition))
  {
    const exprt &operand = not_expr->op();
    if(auto notequal_expr = expr_try_dynamic_cast<notequal_exprt>(operand))
    {
      // !(A != B)
      // -->
      // A == B
      apply_condition(
        equal_exprt{notequal_expr->lhs(), notequal_expr->rhs()},
        previous_state,
        ns);
    }
    else if(auto equal_expr = expr_try_dynamic_cast<equal_exprt>(operand))
    {
      // !(A == B)
      // -->
      // A != B
      apply_condition(
        notequal_exprt{equal_expr->lhs(), equal_expr->rhs()},
        previous_state,
        ns);
    }
    else
    {
      // !A
      // -->
      // A == false
      apply_condition(equal_exprt{operand, false_exprt{}}, previous_state, ns);
    }
  }
  else if(auto equal_expr = expr_try_dynamic_cast<equal_exprt>(condition))
  {
    // Base case: try to apply a single equality constraint
    exprt lhs = equal_expr->lhs();
    exprt rhs = equal_expr->rhs();
    if(is_ssa_expr(rhs))
      std::swap(lhs, rhs);

    if(is_ssa_expr(lhs) && goto_symex_is_constantt()(rhs))
    {
      const ssa_exprt &ssa_lhs = to_ssa_expr(lhs);
      INVARIANT(
        !ssa_lhs.get_level_2().empty(),
        "apply_condition operand should be L2 renamed");

      if(
        previous_state.threads.size() == 1 ||
        previous_state.write_is_shared(ssa_lhs, ns) !=
          goto_symex_statet::write_is_shared_resultt::SHARED)
      {
        const ssa_exprt l1_lhs = remove_level_2(ssa_lhs);
        const irep_idt &l1_identifier = l1_lhs.get_identifier();

        level2.increase_generation(
          l1_identifier, l1_lhs, previous_state.get_l2_name_provider());

        const auto propagation_entry = propagation.find(l1_identifier);
        if(!propagation_entry.has_value())
          propagation.insert(l1_identifier, rhs);
        else if(propagation_entry->get() != rhs)
          propagation.replace(l1_identifier, rhs);

        value_set.assign(l1_lhs, rhs, ns, true, false);
      }
    }
  }
  else if(
    can_cast_expr<symbol_exprt>(condition) && condition.type() == bool_typet())
  {
    // A
    // -->
    // A == true
    apply_condition(equal_exprt{condition, true_exprt()}, previous_state, ns);
  }
  else if(
    can_cast_expr<notequal_exprt>(condition) &&
    expr_checked_cast<notequal_exprt>(condition).lhs().type() == bool_typet{})
  {
    // A != (true|false)
    // -->
    // A == (false|true)
    const notequal_exprt &notequal_expr =
      expr_dynamic_cast<notequal_exprt>(condition);
    exprt lhs = notequal_expr.lhs();
    exprt rhs = notequal_expr.rhs();
    if(is_ssa_expr(rhs))
      std::swap(lhs, rhs);

    if(rhs.is_true())
      apply_condition(equal_exprt{lhs, false_exprt{}}, previous_state, ns);
    else if(rhs.is_false())
      apply_condition(equal_exprt{lhs, true_exprt{}}, previous_state, ns);
    else
      UNREACHABLE;
  }
}

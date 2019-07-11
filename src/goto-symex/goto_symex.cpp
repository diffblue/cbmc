/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include "expr_skeleton.h"
#include "symex_assign.h"

#include <util/format_expr.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>

unsigned goto_symext::dynamic_counter=0;

void goto_symext::do_simplify(exprt &expr)
{
  if(symex_config.simplify_opt)
    simplify(expr, ns);
}

void goto_symext::symex_assign(statet &state, const code_assignt &code)
{
  exprt lhs = clean_expr(code.lhs(), state, true);
  exprt rhs = clean_expr(code.rhs(), state, false);

  DATA_INVARIANT(
    lhs.type() == rhs.type(), "assignments must be type consistent");

  log.conditional_output(
    log.debug(), [this, &lhs](messaget::mstreamt &mstream) {
      mstream << "Assignment to " << format(lhs) << " ["
              << pointer_offset_bits(lhs.type(), ns).value_or(0) << " bits]"
              << messaget::eom;
    });

  if(rhs.id() == ID_side_effect)
  {
    const side_effect_exprt &side_effect_expr = to_side_effect_expr(rhs);
    const irep_idt &statement = side_effect_expr.get_statement();

    if(
      statement == ID_cpp_new || statement == ID_cpp_new_array ||
      statement == ID_java_new_array_data)
    {
      symex_cpp_new(state, lhs, side_effect_expr);
    }
    else if(statement == ID_allocate)
      symex_allocate(state, lhs, side_effect_expr);
    else if(statement == ID_va_start)
      symex_va_start(state, lhs, side_effect_expr);
    else
      UNREACHABLE;
  }
  else
  {
    assignment_typet assignment_type = symex_targett::assignment_typet::STATE;

    // Let's hide return value assignments.
    if(
      lhs.id() == ID_symbol &&
      id2string(to_symbol_expr(lhs).get_identifier()).find("#return_value!") !=
        std::string::npos)
    {
      assignment_type = symex_targett::assignment_typet::HIDDEN;
    }

    // We hide if we are in a hidden function.
    if(state.call_stack().top().hidden_function)
      assignment_type = symex_targett::assignment_typet::HIDDEN;

    // We hide if we are executing a hidden instruction.
    if(state.source.pc->source_location.get_hide())
      assignment_type = symex_targett::assignment_typet::HIDDEN;

    exprt::operandst lhs_if_then_else_conditions;
    symex_assignt{state, assignment_type, ns, symex_config, target}.assign_rec(
      lhs, expr_skeletont{lhs.type()}, rhs, lhs_if_then_else_conditions);
  }
}

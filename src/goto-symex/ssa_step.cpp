/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier <romain.brenguier@diffblue.com>

*******************************************************************/

#include "ssa_step.h"

#include <util/format_expr.h>

void SSA_stept::output(std::ostream &out) const
{
  out << "Thread " << source.thread_nr;

  if(source.pc->source_location.is_not_nil())
    out << " " << source.pc->source_location << '\n';
  else
    out << '\n';

  switch(type)
  {
  case goto_trace_stept::typet::ASSERT:
    out << "ASSERT " << format(cond_expr) << '\n';
    break;
  case goto_trace_stept::typet::ASSUME:
    out << "ASSUME " << format(cond_expr) << '\n';
    break;
  case goto_trace_stept::typet::LOCATION:
    out << "LOCATION" << '\n';
    break;
  case goto_trace_stept::typet::INPUT:
    out << "INPUT" << '\n';
    break;
  case goto_trace_stept::typet::OUTPUT:
    out << "OUTPUT" << '\n';
    break;

  case goto_trace_stept::typet::DECL:
    out << "DECL" << '\n';
    out << format(ssa_lhs) << '\n';
    break;

  case goto_trace_stept::typet::ASSIGNMENT:
    out << "ASSIGNMENT (";
    switch(assignment_type)
    {
    case symex_targett::assignment_typet::HIDDEN:
      out << "HIDDEN";
      break;
    case symex_targett::assignment_typet::STATE:
      out << "STATE";
      break;
    case symex_targett::assignment_typet::VISIBLE_ACTUAL_PARAMETER:
      out << "VISIBLE_ACTUAL_PARAMETER";
      break;
    case symex_targett::assignment_typet::HIDDEN_ACTUAL_PARAMETER:
      out << "HIDDEN_ACTUAL_PARAMETER";
      break;
    case symex_targett::assignment_typet::PHI:
      out << "PHI";
      break;
    case symex_targett::assignment_typet::GUARD:
      out << "GUARD";
      break;
    default:
    {
    }
    }

    out << ")\n";
    break;

  case goto_trace_stept::typet::DEAD:
    out << "DEAD\n";
    break;
  case goto_trace_stept::typet::FUNCTION_CALL:
    out << "FUNCTION_CALL\n";
    break;
  case goto_trace_stept::typet::FUNCTION_RETURN:
    out << "FUNCTION_RETURN\n";
    break;
  case goto_trace_stept::typet::CONSTRAINT:
    out << "CONSTRAINT\n";
    break;
  case goto_trace_stept::typet::SHARED_READ:
    out << "SHARED READ\n";
    break;
  case goto_trace_stept::typet::SHARED_WRITE:
    out << "SHARED WRITE\n";
    break;
  case goto_trace_stept::typet::ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN\n";
    break;
  case goto_trace_stept::typet::ATOMIC_END:
    out << "AUTOMIC_END\n";
    break;
  case goto_trace_stept::typet::SPAWN:
    out << "SPAWN\n";
    break;
  case goto_trace_stept::typet::MEMORY_BARRIER:
    out << "MEMORY_BARRIER\n";
    break;
  case goto_trace_stept::typet::GOTO:
    out << "IF " << format(cond_expr) << " GOTO\n";
    break;

  case goto_trace_stept::typet::NONE:
    UNREACHABLE;
  }

  if(is_assert() || is_assume() || is_assignment() || is_constraint())
    out << format(cond_expr) << '\n';

  if(is_assert() || is_constraint())
    out << comment << '\n';

  if(is_shared_read() || is_shared_write())
    out << format(ssa_lhs) << '\n';

  out << "Guard: " << format(guard) << '\n';
}

/// Check that the SSA step is well-formed
/// \param ns: namespace to lookup identifiers
/// \param vm: validation mode to be used for reporting failures
void SSA_stept::validate(const namespacet &ns, const validation_modet vm) const
{
  validate_full_expr(guard, ns, vm);

  switch(type)
  {
  case goto_trace_stept::typet::ASSERT:
  case goto_trace_stept::typet::ASSUME:
  case goto_trace_stept::typet::GOTO:
  case goto_trace_stept::typet::CONSTRAINT:
    validate_full_expr(cond_expr, ns, vm);
    break;
  case goto_trace_stept::typet::DECL:
    validate_full_expr(ssa_lhs, ns, vm);
    validate_full_expr(ssa_full_lhs, ns, vm);
    validate_full_expr(original_full_lhs, ns, vm);
    break;
  case goto_trace_stept::typet::ASSIGNMENT:
    validate_full_expr(ssa_lhs, ns, vm);
    validate_full_expr(ssa_full_lhs, ns, vm);
    validate_full_expr(original_full_lhs, ns, vm);
    validate_full_expr(ssa_rhs, ns, vm);
    DATA_CHECK(
      vm,
      ssa_lhs.get_original_expr().type() == ssa_rhs.type(),
      "Type inequality in SSA assignment\nlhs-type: " +
        ssa_lhs.get_original_expr().type().id_string() +
        "\nrhs-type: " + ssa_rhs.type().id_string());
    break;
  case goto_trace_stept::typet::INPUT:
  case goto_trace_stept::typet::OUTPUT:
    for(const auto &expr : io_args)
      validate_full_expr(expr, ns, vm);
    break;
  case goto_trace_stept::typet::FUNCTION_CALL:
    for(const auto &expr : ssa_function_arguments)
      validate_full_expr(expr, ns, vm);
  case goto_trace_stept::typet::FUNCTION_RETURN:
  {
    const symbolt *symbol;
    DATA_CHECK(
      vm,
      called_function.empty() || !ns.lookup(called_function, symbol),
      "unknown function identifier " + id2string(called_function));
  }
  break;
  case goto_trace_stept::typet::NONE:
  case goto_trace_stept::typet::LOCATION:
  case goto_trace_stept::typet::DEAD:
  case goto_trace_stept::typet::SHARED_READ:
  case goto_trace_stept::typet::SHARED_WRITE:
  case goto_trace_stept::typet::SPAWN:
  case goto_trace_stept::typet::MEMORY_BARRIER:
  case goto_trace_stept::typet::ATOMIC_BEGIN:
  case goto_trace_stept::typet::ATOMIC_END:
    break;
  }
}

irep_idt SSA_stept::get_property_id() const
{
  PRECONDITION(is_assert());

  irep_idt property_id;

  if(source.pc->is_assert())
  {
    property_id = source.pc->source_location.get_property_id();
  }
  else if(source.pc->is_goto())
  {
    // this is likely an unwinding assertion
    property_id = id2string(source.pc->source_location.get_function()) +
                  ".unwind." + std::to_string(source.pc->loop_number);
  }
  else if(source.pc->is_function_call())
  {
    // this is likely a recursion unwinding assertion
    property_id =
      id2string(source.pc->source_location.get_function()) + ".recursion";
  }
  else
  {
    UNREACHABLE;
  }

  return property_id;
}

SSA_assignment_stept::SSA_assignment_stept(
  symex_targett::sourcet source,
  exprt _guard,
  ssa_exprt _ssa_lhs,
  exprt _ssa_full_lhs,
  exprt _original_full_lhs,
  exprt _ssa_rhs,
  symex_targett::assignment_typet _assignment_type)
  : SSA_stept(source, goto_trace_stept::typet::ASSIGNMENT)
{
  guard = std::move(_guard);
  ssa_lhs = std::move(_ssa_lhs);
  ssa_full_lhs = std::move(_ssa_full_lhs);
  original_full_lhs = std::move(_original_full_lhs);
  ssa_rhs = std::move(_ssa_rhs);
  assignment_type = _assignment_type;
  cond_expr = equal_exprt{ssa_lhs, ssa_rhs};
  hidden = assignment_type != symex_targett::assignment_typet::STATE &&
           assignment_type !=
             symex_targett::assignment_typet::VISIBLE_ACTUAL_PARAMETER;
}

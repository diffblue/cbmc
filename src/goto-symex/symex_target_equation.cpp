/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "symex_target_equation.h"

#include <cassert>

#include <util/std_expr.h>

#include <langapi/language_util.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/prop/prop.h>
#include <solvers/prop/literal_expr.h>

#include "goto_symex_state.h"

symex_target_equationt::symex_target_equationt(
  const namespacet &_ns):ns(_ns)
{
}

symex_target_equationt::~symex_target_equationt()
{
}

/// read from a shared variable
void symex_target_equationt::shared_read(
  const exprt &guard,
  const ssa_exprt &ssa_object,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.ssa_lhs=ssa_object;
  SSA_step.type=goto_trace_stept::typet::SHARED_READ;
  SSA_step.atomic_section_id=atomic_section_id;
  SSA_step.source=source;

  merge_ireps(SSA_step);
}

/// write to a sharedvariable
void symex_target_equationt::shared_write(
  const exprt &guard,
  const ssa_exprt &ssa_object,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.ssa_lhs=ssa_object;
  SSA_step.type=goto_trace_stept::typet::SHARED_WRITE;
  SSA_step.atomic_section_id=atomic_section_id;
  SSA_step.source=source;

  merge_ireps(SSA_step);
}

/// spawn a new thread
void symex_target_equationt::spawn(
  const exprt &guard,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;
  SSA_step.type=goto_trace_stept::typet::SPAWN;
  SSA_step.source=source;

  merge_ireps(SSA_step);
}

void symex_target_equationt::memory_barrier(
  const exprt &guard,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;
  SSA_step.type=goto_trace_stept::typet::MEMORY_BARRIER;
  SSA_step.source=source;

  merge_ireps(SSA_step);
}

/// start an atomic section
void symex_target_equationt::atomic_begin(
  const exprt &guard,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;
  SSA_step.type=goto_trace_stept::typet::ATOMIC_BEGIN;
  SSA_step.atomic_section_id=atomic_section_id;
  SSA_step.source=source;

  merge_ireps(SSA_step);
}

/// end an atomic section
void symex_target_equationt::atomic_end(
  const exprt &guard,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;
  SSA_step.type=goto_trace_stept::typet::ATOMIC_END;
  SSA_step.atomic_section_id=atomic_section_id;
  SSA_step.source=source;

  merge_ireps(SSA_step);
}

/// write to a variable
void symex_target_equationt::assignment(
  const exprt &guard,
  const ssa_exprt &ssa_lhs,
  const exprt &ssa_full_lhs,
  const exprt &original_full_lhs,
  const exprt &ssa_rhs,
  const sourcet &source,
  assignment_typet assignment_type)
{
  assert(ssa_lhs.is_not_nil());

  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.ssa_lhs=ssa_lhs;
  SSA_step.ssa_full_lhs=ssa_full_lhs;
  SSA_step.original_full_lhs=original_full_lhs;
  SSA_step.ssa_rhs=ssa_rhs;
  SSA_step.assignment_type=assignment_type;

  SSA_step.cond_expr=equal_exprt(SSA_step.ssa_lhs, SSA_step.ssa_rhs);
  SSA_step.type=goto_trace_stept::typet::ASSIGNMENT;
  SSA_step.hidden=(assignment_type!=assignment_typet::STATE &&
                   assignment_type!=assignment_typet::VISIBLE_ACTUAL_PARAMETER);
  SSA_step.source=source;

  merge_ireps(SSA_step);
}

/// declare a fresh variable
void symex_target_equationt::decl(
  const exprt &guard,
  const ssa_exprt &ssa_lhs,
  const sourcet &source,
  assignment_typet assignment_type)
{
  assert(ssa_lhs.is_not_nil());

  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.ssa_lhs=ssa_lhs;
  SSA_step.ssa_full_lhs=ssa_lhs;
  SSA_step.original_full_lhs=ssa_lhs.get_original_expr();
  SSA_step.type=goto_trace_stept::typet::DECL;
  SSA_step.source=source;
  SSA_step.hidden=(assignment_type!=assignment_typet::STATE);

  // the condition is trivially true, and only
  // there so we see the symbols
  SSA_step.cond_expr=equal_exprt(SSA_step.ssa_lhs, SSA_step.ssa_lhs);

  merge_ireps(SSA_step);
}

/// declare a fresh variable
void symex_target_equationt::dead(
  const exprt &guard,
  const ssa_exprt &ssa_lhs,
  const sourcet &source)
{
  // we currently don't record these
}

/// just record a location
void symex_target_equationt::location(
  const exprt &guard,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.type=goto_trace_stept::typet::LOCATION;
  SSA_step.source=source;

  merge_ireps(SSA_step);
}

/// just record a location
void symex_target_equationt::function_call(
  const exprt &guard,
  const irep_idt &identifier,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.type=goto_trace_stept::typet::FUNCTION_CALL;
  SSA_step.source=source;
  SSA_step.identifier=identifier;

  merge_ireps(SSA_step);
}

/// just record a location
void symex_target_equationt::function_return(
  const exprt &guard,
  const irep_idt &identifier,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.type=goto_trace_stept::typet::FUNCTION_RETURN;
  SSA_step.source=source;
  SSA_step.identifier=identifier;

  merge_ireps(SSA_step);
}

/// just record output
void symex_target_equationt::output(
  const exprt &guard,
  const sourcet &source,
  const irep_idt &output_id,
  const std::list<exprt> &args)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.type=goto_trace_stept::typet::OUTPUT;
  SSA_step.source=source;
  SSA_step.io_args=args;
  SSA_step.io_id=output_id;

  merge_ireps(SSA_step);
}

/// just record formatted output
void symex_target_equationt::output_fmt(
  const exprt &guard,
  const sourcet &source,
  const irep_idt &output_id,
  const irep_idt &fmt,
  const std::list<exprt> &args)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.type=goto_trace_stept::typet::OUTPUT;
  SSA_step.source=source;
  SSA_step.io_args=args;
  SSA_step.io_id=output_id;
  SSA_step.formatted=true;
  SSA_step.format_string=fmt;

  merge_ireps(SSA_step);
}

/// just record input
void symex_target_equationt::input(
  const exprt &guard,
  const sourcet &source,
  const irep_idt &input_id,
  const std::list<exprt> &args)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.type=goto_trace_stept::typet::INPUT;
  SSA_step.source=source;
  SSA_step.io_args=args;
  SSA_step.io_id=input_id;

  merge_ireps(SSA_step);
}

/// record an assumption
void symex_target_equationt::assumption(
  const exprt &guard,
  const exprt &cond,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.cond_expr=cond;
  SSA_step.type=goto_trace_stept::typet::ASSUME;
  SSA_step.source=source;

  merge_ireps(SSA_step);
}

/// record an assertion
void symex_target_equationt::assertion(
  const exprt &guard,
  const exprt &cond,
  const std::string &msg,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.cond_expr=cond;
  SSA_step.type=goto_trace_stept::typet::ASSERT;
  SSA_step.source=source;
  SSA_step.comment=msg;

  merge_ireps(SSA_step);
}

/// record a goto instruction
void symex_target_equationt::goto_instruction(
  const exprt &guard,
  const exprt &cond,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.cond_expr=cond;
  SSA_step.type=goto_trace_stept::typet::GOTO;
  SSA_step.source=source;

  merge_ireps(SSA_step);
}

/// record a constraint
void symex_target_equationt::constraint(
  const exprt &cond,
  const std::string &msg,
  const sourcet &source)
{
  // like assumption, but with global effect
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=true_exprt();
  SSA_step.cond_expr=cond;
  SSA_step.type=goto_trace_stept::typet::CONSTRAINT;
  SSA_step.source=source;
  SSA_step.comment=msg;

  merge_ireps(SSA_step);
}

void symex_target_equationt::convert(
  prop_convt &prop_conv)
{
  convert_guards(prop_conv);
  convert_assignments(prop_conv);
  convert_decls(prop_conv);
  convert_assumptions(prop_conv);
  convert_assertions(prop_conv);
  convert_goto_instructions(prop_conv);
  convert_io(prop_conv);
  convert_constraints(prop_conv);
}

/// converts assignments
/// \par parameters: decision procedure
/// \return -
void symex_target_equationt::convert_assignments(
  decision_proceduret &decision_procedure) const
{
  for(const auto &step : SSA_steps)
  {
    if(step.is_assignment() && !step.ignore)
      decision_procedure.set_to_true(step.cond_expr);
  }
}

/// converts declarations
/// \return -
void symex_target_equationt::convert_decls(
  prop_convt &prop_conv) const
{
  for(const auto &step : SSA_steps)
  {
    if(step.is_decl() && !step.ignore)
    {
      // The result is not used, these have no impact on
      // the satisfiability of the formula.
      prop_conv.convert(step.cond_expr);
    }
  }
}

/// converts guards
/// \return -
void symex_target_equationt::convert_guards(
  prop_convt &prop_conv)
{
  for(auto &step : SSA_steps)
  {
    if(step.ignore)
      step.guard_literal=const_literal(false);
    else
      step.guard_literal=prop_conv.convert(step.guard);
  }
}

/// converts assumptions
/// \return -
void symex_target_equationt::convert_assumptions(
  prop_convt &prop_conv)
{
  for(auto &step : SSA_steps)
  {
    if(step.is_assume())
    {
      if(step.ignore)
        step.cond_literal=const_literal(true);
      else
        step.cond_literal=prop_conv.convert(step.cond_expr);
    }
  }
}

/// converts goto instructions
/// \return -
void symex_target_equationt::convert_goto_instructions(
  prop_convt &prop_conv)
{
  for(auto &step : SSA_steps)
  {
    if(step.is_goto())
    {
      if(step.ignore)
        step.cond_literal=const_literal(true);
      else
        step.cond_literal=prop_conv.convert(step.cond_expr);
    }
  }
}

/// converts constraints
/// \par parameters: decision procedure
/// \return -
void symex_target_equationt::convert_constraints(
  decision_proceduret &decision_procedure) const
{
  for(const auto &step : SSA_steps)
  {
    if(step.is_constraint())
    {
      if(step.ignore)
        continue;

      decision_procedure.set_to_true(step.cond_expr);
    }
  }
}

/// converts assertions
/// \return -
void symex_target_equationt::convert_assertions(
  prop_convt &prop_conv)
{
  // we find out if there is only _one_ assertion,
  // which allows for a simpler formula

  unsigned number_of_assertions=count_assertions();

  if(number_of_assertions==0)
    return;

  if(number_of_assertions==1)
  {
    for(auto &step : SSA_steps)
    {
      if(step.is_assert())
      {
        prop_conv.set_to_false(step.cond_expr);
        step.cond_literal=const_literal(false);
        return; // prevent further assumptions!
      }
      else if(step.is_assume())
        prop_conv.set_to_true(step.cond_expr);
    }

    assert(false); // unreachable
  }

  // We do (NOT a1) OR (NOT a2) ...
  // where the a's are the assertions
  or_exprt::operandst disjuncts;
  disjuncts.reserve(number_of_assertions);

  exprt assumption=true_exprt();

  for(auto &step : SSA_steps)
  {
    if(step.is_assert())
    {
      implies_exprt implication(
        assumption,
        step.cond_expr);

      // do the conversion
      step.cond_literal=prop_conv.convert(implication);

      // store disjunct
      disjuncts.push_back(literal_exprt(!step.cond_literal));
    }
    else if(step.is_assume())
    {
      // the assumptions have been converted before
      // avoid deep nesting of ID_and expressions
      if(assumption.id()==ID_and)
        assumption.copy_to_operands(literal_exprt(step.cond_literal));
      else
        assumption=
          and_exprt(assumption, literal_exprt(step.cond_literal));
    }
  }

  // the below is 'true' if there are no assertions
  prop_conv.set_to_true(disjunction(disjuncts));
}

/// converts I/O
/// \par parameters: decision procedure
/// \return -
void symex_target_equationt::convert_io(
  decision_proceduret &dec_proc)
{
  unsigned io_count=0;

  for(auto &step : SSA_steps)
    if(!step.ignore)
    {
      for(const auto &arg : step.io_args)
      {
        if(arg.is_constant() ||
           arg.id()==ID_string_constant)
          step.converted_io_args.push_back(arg);
        else
        {
          symbol_exprt symbol;
          symbol.type()=arg.type();
          symbol.set_identifier("symex::io::"+std::to_string(io_count++));

          equal_exprt eq(arg, symbol);
          merge_irep(eq);

          dec_proc.set_to(eq, true);
          step.converted_io_args.push_back(symbol);
        }
      }
    }
}


void symex_target_equationt::merge_ireps(SSA_stept &SSA_step)
{
  merge_irep(SSA_step.guard);

  merge_irep(SSA_step.ssa_lhs);
  merge_irep(SSA_step.ssa_full_lhs);
  merge_irep(SSA_step.original_full_lhs);
  merge_irep(SSA_step.ssa_rhs);

  merge_irep(SSA_step.cond_expr);

  for(auto &step : SSA_step.io_args)
    merge_irep(step);

  // converted_io_args is merged in convert_io
}

void symex_target_equationt::output(std::ostream &out) const
{
  for(const auto &step : SSA_steps)
  {
    step.output(ns, out);
    out << "--------------\n";
  }
}

void symex_target_equationt::SSA_stept::output(
  const namespacet &ns,
  std::ostream &out) const
{
  if(source.is_set)
  {
    out << "Thread " << source.thread_nr;

    if(source.pc->source_location.is_not_nil())
      out << " " << source.pc->source_location << '\n';
    else
      out << '\n';
  }

  switch(type)
  {
  case goto_trace_stept::typet::ASSERT:
    out << "ASSERT " << from_expr(ns, "", cond_expr) << '\n'; break;
  case goto_trace_stept::typet::ASSUME:
    out << "ASSUME " << from_expr(ns, "", cond_expr) << '\n'; break;
  case goto_trace_stept::typet::LOCATION:
    out << "LOCATION" << '\n'; break;
  case goto_trace_stept::typet::INPUT:
    out << "INPUT" << '\n'; break;
  case goto_trace_stept::typet::OUTPUT:
    out << "OUTPUT" << '\n'; break;

  case goto_trace_stept::typet::DECL:
    out << "DECL" << '\n';
    out << from_expr(ns, "", ssa_lhs) << '\n';
    break;

  case goto_trace_stept::typet::ASSIGNMENT:
    out << "ASSIGNMENT (";
    switch(assignment_type)
    {
    case assignment_typet::HIDDEN:
      out << "HIDDEN"; break;
    case assignment_typet::STATE:
      out << "STATE"; break;
    case assignment_typet::VISIBLE_ACTUAL_PARAMETER:
      out << "VISIBLE_ACTUAL_PARAMETER"; break;
    case assignment_typet::HIDDEN_ACTUAL_PARAMETER:
      out << "HIDDEN_ACTUAL_PARAMETER"; break;
    case assignment_typet::PHI:
      out << "PHI"; break;
    case assignment_typet::GUARD:
      out << "GUARD"; break;
    default:
      {
      }
    }

    out << ")\n";
    break;

  case goto_trace_stept::typet::DEAD:
    out << "DEAD\n"; break;
  case goto_trace_stept::typet::FUNCTION_CALL:
    out << "FUNCTION_CALL\n"; break;
  case goto_trace_stept::typet::FUNCTION_RETURN:
    out << "FUNCTION_RETURN\n"; break;
  case goto_trace_stept::typet::CONSTRAINT:
    out << "CONSTRAINT\n"; break;
  case goto_trace_stept::typet::SHARED_READ:
    out << "SHARED READ\n"; break;
  case goto_trace_stept::typet::SHARED_WRITE:
    out << "SHARED WRITE\n"; break;
  case goto_trace_stept::typet::ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN\n"; break;
  case goto_trace_stept::typet::ATOMIC_END:
    out << "AUTOMIC_END\n"; break;
  case goto_trace_stept::typet::SPAWN:
    out << "SPAWN\n"; break;
  case goto_trace_stept::typet::MEMORY_BARRIER:
    out << "MEMORY_BARRIER\n"; break;
  case goto_trace_stept::typet::GOTO:
    out << "IF " << from_expr(ns, "", cond_expr) << " GOTO\n"; break;

  default: assert(false);
  }

  if(is_assert() || is_assume() || is_assignment() || is_constraint())
    out << from_expr(ns, "", cond_expr) << '\n';

  if(is_assert() || is_constraint())
    out << comment << '\n';

  if(is_shared_read() || is_shared_write())
    out << from_expr(ns, "", ssa_lhs) << '\n';

  out << "Guard: " << from_expr(ns, "", guard) << '\n';
}

std::ostream &operator<<(
  std::ostream &out,
  const symex_target_equationt &equation)
{
  equation.output(out);
  return out;
}

std::ostream &operator<<(
  std::ostream &out,
  const symex_target_equationt::SSA_stept &step)
{
  // may cause lookup failures, since it's blank
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  step.output(ns, out);
  return out;
}

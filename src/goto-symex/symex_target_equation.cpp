/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <i2string.h>
#include <std_expr.h>
#include <expr_util.h>

#include <langapi/language_util.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/prop/prop.h>

#include "goto_symex_state.h"
#include "symex_target_equation.h"

/*******************************************************************\

Function: symex_target_equationt::assignment

  Inputs:

 Outputs:

 Purpose: write to a variable

\*******************************************************************/

void symex_target_equationt::assignment(
  const guardt &guard,
  const symbol_exprt &ssa_lhs,
  const symbol_exprt &original_lhs_object,
  const exprt &ssa_full_lhs,
  const exprt &original_full_lhs,
  const exprt &ssa_rhs,
  const sourcet &source,
  assignment_typet assignment_type)
{
  assert(ssa_lhs.is_not_nil());
  
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  
  SSA_step.guard_expr=guard.as_expr();
  SSA_step.ssa_lhs=ssa_lhs;
  SSA_step.original_lhs_object=original_lhs_object;
  SSA_step.ssa_full_lhs=ssa_full_lhs;
  SSA_step.original_full_lhs=original_full_lhs;
  SSA_step.ssa_rhs=ssa_rhs;
  SSA_step.assignment_type=assignment_type;

  SSA_step.cond_expr=equal_exprt(SSA_step.ssa_lhs, SSA_step.ssa_rhs);
  SSA_step.type=goto_trace_stept::ASSIGNMENT;
  SSA_step.source=source;
}

/*******************************************************************\

Function: symex_target_equationt::decl

  Inputs:

 Outputs:

 Purpose: declare a fresh variable

\*******************************************************************/

void symex_target_equationt::decl(
  const guardt &guard,
  const symbol_exprt &ssa_lhs,
  const symbol_exprt &original_lhs_object,
  const sourcet &source)
{
  assert(ssa_lhs.is_not_nil());
  
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  
  SSA_step.guard_expr=guard.as_expr();
  SSA_step.ssa_lhs=ssa_lhs;
  SSA_step.ssa_full_lhs=ssa_lhs;
  SSA_step.original_lhs_object=original_lhs_object;
  SSA_step.original_full_lhs=original_lhs_object;
  SSA_step.type=goto_trace_stept::DECL;
  SSA_step.source=source;

  // the condition is trivially true, and only
  // there so we see the symbols
  SSA_step.cond_expr=equal_exprt(SSA_step.ssa_lhs, SSA_step.ssa_lhs);
}

/*******************************************************************\

Function: symex_target_equationt::dead

  Inputs:

 Outputs:

 Purpose: declare a fresh variable

\*******************************************************************/

void symex_target_equationt::dead(
  const guardt &guard,
  const symbol_exprt &ssa_lhs,
  const symbol_exprt &original_lhs_object,
  const sourcet &source)
{
  // we currently don't record these
}

/*******************************************************************\

Function: symex_target_equationt::location

  Inputs:

 Outputs:

 Purpose: just record a location

\*******************************************************************/

void symex_target_equationt::location(
  const guardt &guard,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  
  SSA_step.guard_expr=guard.as_expr();
  SSA_step.type=goto_trace_stept::LOCATION;
  SSA_step.source=source;
}

/*******************************************************************\

Function: symex_target_equationt::function_call

  Inputs:

 Outputs:

 Purpose: just record a location

\*******************************************************************/

void symex_target_equationt::function_call(
  const guardt &guard,
  const irep_idt &identifier,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  
  SSA_step.guard_expr=guard.as_expr();
  SSA_step.type=goto_trace_stept::FUNCTION_CALL;
  SSA_step.source=source;
  SSA_step.identifier=identifier;
}

/*******************************************************************\

Function: symex_target_equationt::function_return

  Inputs:

 Outputs:

 Purpose: just record a location

\*******************************************************************/

void symex_target_equationt::function_return(
  const guardt &guard,
  const irep_idt &identifier,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  
  SSA_step.guard_expr=guard.as_expr();
  SSA_step.type=goto_trace_stept::FUNCTION_RETURN;
  SSA_step.source=source;
  SSA_step.identifier=identifier;
}

/*******************************************************************\

Function: symex_target_equationt::output

  Inputs:

 Outputs:

 Purpose: just record output

\*******************************************************************/

void symex_target_equationt::output(
  const guardt &guard,
  const sourcet &source,
  const irep_idt &output_id,
  const std::list<exprt> &args)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  
  SSA_step.guard_expr=guard.as_expr();
  SSA_step.type=goto_trace_stept::OUTPUT;
  SSA_step.source=source;
  SSA_step.io_args=args;
  SSA_step.io_id=output_id;
}

/*******************************************************************\

Function: symex_target_equationt::output_fmt

  Inputs:

 Outputs:

 Purpose: just record formatted output

\*******************************************************************/

void symex_target_equationt::output_fmt(
  const guardt &guard,
  const sourcet &source,
  const irep_idt &output_id,
  const irep_idt &fmt,
  const std::list<exprt> &args)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  
  SSA_step.guard_expr=guard.as_expr();
  SSA_step.type=goto_trace_stept::OUTPUT;
  SSA_step.source=source;
  SSA_step.io_args=args;
  SSA_step.io_id=output_id;
  SSA_step.formatted=true;
  SSA_step.format_string=fmt;
}

/*******************************************************************\

Function: symex_target_equationt::input

  Inputs:

 Outputs:

 Purpose: just record input

\*******************************************************************/

void symex_target_equationt::input(
  const guardt &guard,
  const sourcet &source,
  const irep_idt &input_id,
  const std::list<exprt> &args)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  
  SSA_step.guard_expr=guard.as_expr();
  SSA_step.type=goto_trace_stept::INPUT;
  SSA_step.source=source;
  SSA_step.io_args=args;
  SSA_step.io_id=input_id;
}

/*******************************************************************\

Function: symex_target_equationt::assumption

  Inputs: 

 Outputs:

 Purpose: record an assumption

\*******************************************************************/

void symex_target_equationt::assumption(
  const guardt &guard,
  const exprt &cond,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  
  SSA_step.guard_expr=guard.as_expr();
  SSA_step.cond_expr=cond;
  SSA_step.type=goto_trace_stept::ASSUME;
  SSA_step.source=source;
}

/*******************************************************************\

Function: symex_target_equationt::assertion

  Inputs:

 Outputs:

 Purpose: record an assertion

\*******************************************************************/

void symex_target_equationt::assertion(
  const guardt &guard,
  const exprt &cond,
  const std::string &msg,
  const sourcet &source)
{
  SSA_steps.push_back(SSA_stept());
  SSA_stept &SSA_step=SSA_steps.back();
  
  SSA_step.guard_expr=guard.as_expr();
  SSA_step.cond_expr=cond;
  SSA_step.type=goto_trace_stept::ASSERT;
  SSA_step.source=source;
  SSA_step.comment=msg;
}

/*******************************************************************\

Function: symex_target_equationt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_target_equationt::convert(
  prop_convt &prop_conv)
{
  convert_guards(prop_conv);
  convert_assignments(prop_conv);
  convert_decls(prop_conv);
  convert_assumptions(prop_conv);
  convert_assertions(prop_conv);
  convert_io(prop_conv);
}

/*******************************************************************\

Function: symex_target_equationt::convert_assignments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_target_equationt::convert_assignments(
  decision_proceduret &decision_procedure) const
{
  for(SSA_stepst::const_iterator it=SSA_steps.begin();
      it!=SSA_steps.end(); it++)
  {
    if(it->is_assignment() && !it->ignore)
      decision_procedure.set_to_true(it->cond_expr);
  }
}

/*******************************************************************\

Function: symex_target_equationt::convert_decls

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_target_equationt::convert_decls(
  prop_convt &prop_conv) const
{
  for(SSA_stepst::const_iterator it=SSA_steps.begin();
      it!=SSA_steps.end(); it++)
  {
    if(it->is_decl() && !it->ignore)
    {
      // The result is not used, these have no impact on
      // the satisfiability of the formula.
      prop_conv.convert(it->cond_expr);
    }
  }
}

/*******************************************************************\

Function: symex_target_equationt::convert_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_target_equationt::convert_guards(
  prop_convt &prop_conv)
{
  for(SSA_stepst::iterator it=SSA_steps.begin();
      it!=SSA_steps.end(); it++)
  {
    if(it->ignore)
      it->guard_literal=const_literal(false);
    else
      it->guard_literal=prop_conv.convert(it->guard_expr);
  }
}

/*******************************************************************\

Function: symex_target_equationt::convert_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_target_equationt::convert_assumptions(
  prop_convt &prop_conv)
{
  for(SSA_stepst::iterator it=SSA_steps.begin();
      it!=SSA_steps.end(); it++)
  {
    if(it->is_assume())
    {
      if(it->ignore)
        it->cond_literal=const_literal(true);
      else
        it->cond_literal=prop_conv.convert(it->cond_expr);
    }
  }
}

/*******************************************************************\

Function: symex_target_equationt::convert_assertions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    for(SSA_stepst::iterator it=SSA_steps.begin();
        it!=SSA_steps.end(); it++)
      if(it->is_assert())
      {
        prop_conv.set_to_false(it->cond_expr);
        it->cond_literal=prop_conv.convert(it->cond_expr);
        return; // prevent further assumptions!
      }
      else if(it->is_assume())
        prop_conv.set_to_true(it->cond_expr);

    assert(false); // unreachable
  }

  bvt bv;

  bv.reserve(number_of_assertions);
  
  literalt assumption_literal=const_literal(true);

  for(SSA_stepst::iterator it=SSA_steps.begin();
      it!=SSA_steps.end(); it++)
    if(it->is_assert())
    {
      // do the expression
      literalt tmp_literal=prop_conv.convert(it->cond_expr);

      it->cond_literal=prop_conv.prop.limplies(assumption_literal, tmp_literal);

      bv.push_back(prop_conv.prop.lnot(it->cond_literal));
    }
    else if(it->is_assume())
      assumption_literal=
        prop_conv.prop.land(assumption_literal, it->cond_literal);

  if(!bv.empty())
    prop_conv.prop.lcnf(bv);
}

/*******************************************************************\

Function: symex_target_equationt::convert_io

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_target_equationt::convert_io(
  decision_proceduret &dec_proc)
{
  unsigned io_count=0;

  for(SSA_stepst::iterator it=SSA_steps.begin();
      it!=SSA_steps.end(); it++)
    if(!it->ignore)
    {
      for(std::list<exprt>::const_iterator
          o_it=it->io_args.begin();
          o_it!=it->io_args.end();
          o_it++)
      {
        exprt tmp=*o_it;
        
        if(tmp.is_constant() ||
           tmp.id()==ID_string_constant)
          it->converted_io_args.push_back(tmp);
        else
        {
          symbol_exprt symbol;
          symbol.type()=tmp.type();
          symbol.set_identifier("symex::io::"+i2string(io_count++));
          dec_proc.set_to(equal_exprt(tmp, symbol), true);
          it->converted_io_args.push_back(symbol);
        }
      }
    }
}

/*******************************************************************\

Function: symex_target_equationt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_target_equationt::output(std::ostream &out) const
{
  for(SSA_stepst::const_iterator
      it=SSA_steps.begin();
      it!=SSA_steps.end();
      it++)
  {
    it->output(ns, out);    
    out << "--------------" << std::endl;
  }
}

/*******************************************************************\

Function: symex_target_equationt::SSA_stept::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_target_equationt::SSA_stept::output(
  const namespacet &ns,
  std::ostream &out) const
{
  if(source.is_set)
  {
    out << "Thread " << source.thread_nr;

    if(source.pc->location.is_not_nil())
      out << " " << source.pc->location << std::endl;
    else
      out << std::endl;
  }

  switch(type)
  {
  case goto_trace_stept::ASSERT: out << "ASSERT" << std::endl; break;
  case goto_trace_stept::ASSUME: out << "ASSUME" << std::endl; break;
  case goto_trace_stept::LOCATION: out << "LOCATION" << std::endl; break;
  case goto_trace_stept::OUTPUT: out << "OUTPUT" << std::endl; break;

  case goto_trace_stept::DECL:
    out << "DECL" << std::endl;
    out << from_expr(ns, "", ssa_lhs) << std::endl;
    break;

  case goto_trace_stept::ASSIGNMENT:
    out << "ASSIGNMENT (";
    switch(assignment_type)
    {
    case HIDDEN: out << "HIDDEN"; break;
    case STATE: out << "STATE"; break;
    default:;
    }

    out << ")" << std::endl;
    break;
    
  case goto_trace_stept::DEAD: out << "DEAD" << std::endl; break;
  case goto_trace_stept::FUNCTION_CALL: out << "FUNCTION_CALL" << std::endl; break;
  case goto_trace_stept::FUNCTION_RETURN: out << "FUNCTION_RETURN" << std::endl; break;

  default: assert(false);
  }

  if(is_assert() || is_assume() || is_assignment())
    out << from_expr(ns, "", cond_expr) << std::endl;
  
  if(is_assert())
    out << comment << std::endl;

  out << "Guard: " << from_expr(ns, "", guard_expr) << std::endl;
}

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator<<(
  std::ostream &out,
  const symex_target_equationt &equation)
{
  equation.output(out);
  return out;
}

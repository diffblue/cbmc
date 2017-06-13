/*******************************************************************\

Module: Remove calls to functions without a body

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Remove calls to functions without a body

#include "remove_calls_nobody.h"

void remove_calls_nobodyt::remove_call_nobody(
  goto_programt &dest,
  goto_programt::targett target,
  const exprt &lhs,
  const exprt::operandst &arguments)
{
  assert(target->is_function_call());
  assert(!dest.empty());

  goto_programt tmp;

  // evaluate function arguments -- they might have
  // pointer dereferencing or the like
  forall_expr(it, arguments)
  {
    goto_programt::targett t=tmp.add_instruction();
    t->make_other(code_expressiont(*it));
    t->source_location=target->source_location;
    t->function=target->function;
  }

  // return value
  if(lhs.is_not_nil())
  {
    side_effect_expr_nondett rhs(lhs.type());
    rhs.add_source_location()=target->source_location;

    code_assignt code(lhs, rhs);
    code.add_source_location()=target->source_location;

    goto_programt::targett t=tmp.add_instruction(ASSIGN);
    t->source_location=target->source_location;
    t->function=target->function;
    t->code.swap(code);
  }

  // kill call
  target->type=LOCATION;
  target->code.clear();
  target++;

  dest.destructive_insert(target, tmp);
}

void remove_calls_nobodyt::remove_calls_nobody(
  goto_programt &goto_program,
  const goto_functionst &goto_functions)
{
  for(goto_programt::targett it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();) // no it++
  {
    if(!it->is_function_call())
    {
      it++;
      continue;
    }

    const code_function_callt &cfc=to_code_function_call(it->code);
    const exprt &f=cfc.function();

    if(f.id()!=ID_symbol)
    {
      it++;
      continue;
    }

    const symbol_exprt &se=to_symbol_expr(f);
    const irep_idt id=se.get_identifier();

    goto_functionst::function_mapt::const_iterator f_it=
      goto_functions.function_map.find(id);

    bool may_have_body=f_it!=goto_functions.function_map.end();

    if(may_have_body)
    {
      const goto_functiont &goto_function=f_it->second;
      may_have_body=goto_function.body_available();
    }

    if(!may_have_body)
    {
      remove_call_nobody(goto_program, it, cfc.lhs(), cfc.arguments());
    }
    else // called function has a body
    {
      it++;
    }
  }
}

void remove_calls_nobodyt::remove_calls_nobody(goto_functionst &goto_functions)
{
  Forall_goto_functions(f_it, goto_functions)
  {
    goto_functiont &goto_function=f_it->second;

    if(goto_function.body_available())
    {
      remove_calls_nobody(goto_function.body, goto_functions);
    }
  }
}

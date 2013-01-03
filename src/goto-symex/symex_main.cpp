/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <std_expr.h>
#include <rename.h>
#include <context.h>

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::new_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::new_name(symbolt &symbol)
{
  get_new_name(symbol, ns);
  new_context.add(symbol);
}

/*******************************************************************\

Function: goto_symext::claim

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::claim(
  const exprt &claim_expr,
  const std::string &msg,
  statet &state)
{
  total_claims++;

  exprt expr=claim_expr;
  state.rename(expr, ns);
  
  // first try simplifier on it
  do_simplify(expr);

  if(expr.is_true()) return;

  // the simplifier might have produced new symbols,
  // rename again
  state.rename(expr, ns);
    
  state.guard.guard_expr(expr);
  
  remaining_claims++;
  target.assertion(state.guard, expr, msg, state.source);
}

/*******************************************************************\

Function: goto_symext::operator()

  Inputs:

 Outputs:

 Purpose: symex from given state

\*******************************************************************/

void goto_symext::operator()(
  statet &state,
  const goto_functionst &goto_functions,
  const goto_programt &goto_program)
{
  assert(!goto_program.instructions.empty());

  state.source=symex_targett::sourcet(goto_program);
  assert(!state.threads.empty());
  assert(!state.call_stack().empty());
  state.top().end_of_function=--goto_program.instructions.end();
  state.top().calling_location.pc=state.top().end_of_function;
  
  assert(state.top().end_of_function->is_end_function());

  while(!state.call_stack().empty())
  {
    symex_step(goto_functions, state);
    
    // is there another thread to execute?
    if(state.call_stack().empty() &&
       state.source.thread_nr+1<state.threads.size())
    {
      unsigned t=state.source.thread_nr+1;
      //std::cout << "********* Now executing thread " << t << std::endl;
      state.switch_to_thread(t);
    }
  }
}

/*******************************************************************\

Function: goto_symext::operator()

  Inputs:

 Outputs:

 Purpose: symex starting from given program

\*******************************************************************/

void goto_symext::operator()(
  const goto_functionst &goto_functions,
  const goto_programt &goto_program)
{
  statet state;
  operator() (state, goto_functions, goto_program);
}

/*******************************************************************\

Function: goto_symext::operator()

  Inputs:

 Outputs:

 Purpose: symex from entry point

\*******************************************************************/

void goto_symext::operator()(const goto_functionst &goto_functions)
{
  goto_functionst::function_mapt::const_iterator it=
    goto_functions.function_map.find(ID_main);

  if(it==goto_functions.function_map.end())
    throw "main symbol not found; please set an entry point";

  const goto_programt &body=it->second.body;

  operator()(goto_functions, body);
}

/*******************************************************************\

Function: goto_symext::symex_step

  Inputs:

 Outputs:

 Purpose: do just one step

\*******************************************************************/

void goto_symext::symex_step(
  const goto_functionst &goto_functions,
  statet &state)
{
  #if 0
  std::cout << "\ninstruction type is " << state.source.pc->type << std::endl;
  std::cout << "Location: " << state.source.pc->location << std::endl;
  std::cout << "Guard: " << from_expr(state.guard.as_expr()) << std::endl;
  // std::cout << state.source.pc->code.pretty(0, 100) << std::endl;
  #endif

  assert(!state.threads.empty());
  assert(!state.call_stack().empty());

  const goto_programt::instructiont &instruction=*state.source.pc;

  merge_gotos(state);

  // depth exceeded?
  {
    unsigned max_depth=options.get_int_option("depth");
    if(max_depth!=0 && state.depth>max_depth)
      state.guard.add(false_exprt());
    state.depth++;
  }

  // actually do instruction
  switch(instruction.type)
  {
  case SKIP:
    // really ignore
    state.source.pc++;
    break;

  case END_FUNCTION:
    symex_end_of_function(state);
    state.source.pc++;
    break;
  
  case LOCATION:
    target.location(state.guard, state.source);
    state.source.pc++;
    break;
  
  case GOTO:
    symex_goto(state);
    break;
    
  case ASSUME:
    if(!state.guard.is_false())
    {
      exprt tmp=instruction.guard;
      clean_expr(tmp, state, false);
      state.rename(tmp, ns);
      do_simplify(tmp);

      if(!tmp.is_true())
      {
        exprt tmp2=tmp;
        state.guard.guard_expr(tmp2);
        target.assumption(state.guard, tmp2, state.source);

        #if 0      
        // we also add it to the state guard
        state.guard.add(tmp);
        #endif
      }
    }

    state.source.pc++;
    break;

  case ASSERT:
    if(!state.guard.is_false())
      if(options.get_bool_option("assertions") ||
         !state.source.pc->location.get_bool("user-provided"))
      {
        std::string msg=id2string(state.source.pc->location.get_comment());
        if(msg=="") msg="assertion";
        exprt tmp(instruction.guard);
        clean_expr(tmp, state, false);
        claim(tmp, msg, state);
      }

    state.source.pc++;
    break;
    
  case RETURN:
    if(!state.guard.is_false())
      symex_return(state);

    state.source.pc++;
    break;

  case ASSIGN:
    if(!state.guard.is_false())
    {
      code_assignt deref_code=to_code_assign(instruction.code);

      clean_expr(deref_code.lhs(), state, true);
      clean_expr(deref_code.rhs(), state, false);

      symex_assign(state, deref_code);
    }

    state.source.pc++;
    break;

  case FUNCTION_CALL:
    if(!state.guard.is_false())
    {
      code_function_callt deref_code=
        to_code_function_call(instruction.code);

      if(deref_code.lhs().is_not_nil())
        clean_expr(deref_code.lhs(), state, true);

      clean_expr(deref_code.function(), state, false);

      Forall_expr(it, deref_code.arguments())
        clean_expr(*it, state, false);
    
      symex_function_call(goto_functions, state, deref_code);
    }
    else
      state.source.pc++;
    break;

  case OTHER:
    if(!state.guard.is_false())
      symex_other(goto_functions, state);

    state.source.pc++;
    break;

  case DECL:
    if(!state.guard.is_false())
      symex_decl(state);

    state.source.pc++;
    break;

  case DEAD:
    // ignore for now
    state.source.pc++;
    break;

  case START_THREAD:
    symex_start_thread(state);
    state.source.pc++;
    break;
  
  case END_THREAD:
    // behaves like assume(0);
    if(!state.guard.is_false())
      state.guard.add(false_exprt());
    state.source.pc++;
    break;
  
  case ATOMIC_BEGIN:
    state.atomic_section_count++;
    state.source.pc++;
    break;
    
  case ATOMIC_END:
    if(state.atomic_section_count==0)
      throw "ATOMIC_END unmatched";
    state.atomic_section_count--;
    state.source.pc++;
    break;
    
  case CATCH:
    symex_catch(state);
    state.source.pc++;
    break;
  
  case THROW:
    symex_throw(state);
    state.source.pc++;
    break;
    
  case NO_INSTRUCTION_TYPE:
    throw "symex got NO_INSTRUCTION";
  
  default:
    throw "symex got unexpected instruction";
  }
}

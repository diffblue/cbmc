/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <std_expr.h>
#include <rename.h>

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
    
  state.guard.guard_expr(expr);
  
  remaining_claims++;
  target.assertion(state.guard, expr, msg, state.source);
}

/*******************************************************************\

Function: goto_symext::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::operator()(
  statet& state,
  const goto_functionst &goto_functions,
  const goto_programt &goto_program)
{
  state.source.is_set=true;
  state.source.pc=goto_program.instructions.begin();
  state.top().end_of_function=--goto_program.instructions.end();
  state.top().calling_location=state.top().end_of_function;

  while(state.source.pc!=goto_program.instructions.end())
  {
    #if 0
    goto_program.output_instruction(ns, "", std::cout, state.source.pc);
    #endif

    symex_step(goto_functions, state);
  }
}

/*******************************************************************\

Function: goto_symext::operator()

  Inputs:

 Outputs:

 Purpose:

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

 Purpose:

\*******************************************************************/

void goto_symext::operator()(const goto_functionst &goto_functions)
{
  goto_functionst::function_mapt::const_iterator it=
    goto_functions.function_map.find(ID_main);

  if(it==goto_functions.function_map.end())
    throw "main symbol not found; please set an entry point";

  const goto_programt &body=it->second.body;

  statet state;
  state.initialize(goto_functions);

  while(state.source.pc!=body.instructions.end())
    symex_step(goto_functions, state);
}

/*******************************************************************\

Function: goto_symext::symex_step

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_step(
  const goto_functionst &goto_functions,
  statet &state)
{
  #if 0
  std::cout << "\ninstruction type is " << state.source.pc->type << std::endl;
  std::cout << state.source.pc->code.pretty(0, 100) << std::endl;
  #endif

  assert(!state.call_stack.empty());

  const goto_programt::instructiont &instruction=*state.source.pc;

  merge_gotos(state);

  // depth exceeded?
  {
    unsigned max_depth=atoi(options.get_option("depth").c_str());
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

      basic_symext::symex_assign(state, deref_code);
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
    throw "START_THREAD not yet implemented";
  
  case END_THREAD:
    {
      // behaves like assume(0);
      state.guard.add(false_exprt());
      exprt tmp=state.guard.as_expr();
      target.assumption(state.guard, tmp, state.source);
    }
    state.source.pc++;
    break;
  
  case ATOMIC_BEGIN:
  case ATOMIC_END:
    // these don't have path semantics
    state.source.pc++;
    break;
  
  default:
    assert(false);
  }
}

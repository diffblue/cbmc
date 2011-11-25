/*******************************************************************\

Module: Stack depth checks

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

#include <context.h>
#include <std_expr.h>
#include <std_types.h>
#include <arith_tools.h>
#include <cprover_prefix.h>
#include <i2string.h>

#include <goto-programs/goto_functions.h>

#include "stack_depth.h"

/*******************************************************************\

Function: add_stack_depth_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt add_stack_depth_symbol(contextt &context)
{
  const irep_idt identifier="$stack_depth";
  signedbv_typet type(sizeof(int)*8);

  symbolt new_symbol;
  new_symbol.name=identifier;
  new_symbol.base_name=identifier;
  new_symbol.pretty_name=identifier;
  new_symbol.type=type;
  new_symbol.static_lifetime=true;
  new_symbol.value=from_integer(0, type);
  new_symbol.mode=ID_C;
  new_symbol.thread_local=true;
  new_symbol.lvalue=true;

  context.move(new_symbol);

  return symbol_exprt(identifier, type);
}

/*******************************************************************\

Function: stack_depth

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void stack_depth(
  goto_programt &goto_program,
  const symbol_exprt &symbol,
  const int i_depth,
  const exprt &max_depth)
{
  assert(!goto_program.instructions.empty());

  goto_programt::targett first=goto_program.instructions.begin();

  binary_relation_exprt guard(symbol, ID_le, max_depth);
  goto_programt::targett assert_ins=goto_program.insert_before(first);
  assert_ins->make_assertion(guard);
  assert_ins->location=first->location;
  assert_ins->function=first->function;

  assert_ins->location.set_comment("Stack depth exceeds "+i2string(i_depth));
  assert_ins->location.set_property("stack-depth");
  assert_ins->location.set_priority(2); // relatively low

  goto_programt::targett plus_ins=goto_program.insert_before(first);
  plus_ins->make_assignment();
  plus_ins->code=code_assignt(symbol,
      plus_exprt(symbol, from_integer(1, symbol.type())));
  plus_ins->location=first->location;
  plus_ins->function=first->function;

  goto_programt::targett last=--goto_program.instructions.end();
  assert(last->is_end_function());

  goto_programt::instructiont minus_ins;
  minus_ins.make_assignment();
  minus_ins.code=code_assignt(symbol,
      minus_exprt(symbol, from_integer(1, symbol.type())));
  minus_ins.location=last->location;
  minus_ins.function=last->function;

  goto_program.insert_before_swap(last, minus_ins);
}

/*******************************************************************\

Function: stack_depth

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void stack_depth(
  contextt &context,
  goto_functionst &goto_functions,
  const int depth)
{
  const symbol_exprt sym=add_stack_depth_symbol(context);
  const exprt depth_expr(from_integer(depth, sym.type()));

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->second.body_available &&
        f_it->first!=CPROVER_PREFIX "initialize" &&
        f_it->first!=ID_main)
      stack_depth(f_it->second.body, sym, depth, depth_expr);

  // initialize depth to 0
  goto_functionst::function_mapt::iterator
    i_it=goto_functions.function_map.find(CPROVER_PREFIX "initialize");
  assert(i_it!=goto_functions.function_map.end());

  goto_programt &init=i_it->second.body;
  goto_programt::targett first=init.instructions.begin();
  goto_programt::targett it=init.insert_before(first);
  it->make_assignment();
  it->code=code_assignt(sym, from_integer(0, sym.type()));
  it->location=first->location;
  it->function=first->function;

  // update counters etc.
  goto_functions.update();
}


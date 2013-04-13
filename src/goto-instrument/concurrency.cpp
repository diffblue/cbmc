/*******************************************************************\

Module: Encoding for Threaded Goto Programs

Author: Daniel Kroening

Date: October 2012

\*******************************************************************/

#include <util/std_expr.h>
#include <util/find_symbols.h>
#include <util/replace_symbol.h>

#include <analyses/is_threaded.h>

#include "concurrency.h"

class concurrency_instrumentationt
{
public:
  concurrency_instrumentationt(
    value_setst &_value_sets, 
    symbol_tablet &_symbol_table):
    value_sets(_value_sets),
    symbol_table(_symbol_table)
  {
  }
  
  void operator()(goto_functionst &goto_functions)
  {
    instrument(goto_functions);
  }

protected:
  value_setst &value_sets;
  symbol_tablet &symbol_table;

  void instrument(goto_functionst &goto_functions);

  void instrument(
    goto_programt &goto_program,
    const is_threadedt &is_threaded);

  void instrument(exprt &expr);

  void collect(
    const goto_programt &goto_program,
    const is_threadedt &is_threaded);

  void collect(const exprt &expr);

  void add_array_symbols();

  class shared_vart
  {
  public:
    typet type;
    symbol_exprt array_symbol, w_index_symbol;
  };

  class thread_local_vart
  {
  public:
    typet type;
    symbol_exprt array_symbol;
  };

  typedef std::map<irep_idt, shared_vart> shared_varst;
  shared_varst shared_vars;

  typedef std::map<irep_idt, thread_local_vart> thread_local_varst;
  thread_local_varst thread_local_vars;
};

/*******************************************************************\

Function: concurrency_instrumentationt::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concurrency_instrumentationt::instrument(exprt &expr)
{
  std::set<exprt> symbols;

  find_symbols(expr, symbols);

  replace_symbolt replace_symbol;  
  
  for(std::set<exprt>::const_iterator
      s_it=symbols.begin();
      s_it!=symbols.end();
      s_it++)
  {
    if(s_it->id()==ID_symbol)
    {
      const irep_idt identifier=
        to_symbol_expr(*s_it).get_identifier();

      shared_varst::const_iterator
        v_it=shared_vars.find(identifier);
        
      if(v_it!=shared_vars.end())
      {
        index_exprt new_expr;
        //new_expr.array()=symbol_expr();
        //new_expr.index()=symbol_expr();
    
        replace_symbol.insert(identifier, new_expr);
      }
    }
  }
}

/*******************************************************************\

Function: concurrency_instrumentationt::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concurrency_instrumentationt::instrument(
  goto_programt &goto_program,
  const is_threadedt &is_threaded)
{
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(it->is_assign())
    {
      code_assignt &code=to_code_assign(it->code);
      instrument(code.rhs());
    }
    else if(it->is_assume() || it->is_assert() || it->is_goto())
      instrument(it->guard);
    else if(it->is_function_call())
    {
      code_function_callt &code=to_code_function_call(it->code);
      instrument(code.function());

      //instrument(code.lhs(), LHS);
      Forall_expr(it, code.arguments())
        instrument(*it);
    }
  }
}

/*******************************************************************\

Function: concurrency_instrumentationt::collect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concurrency_instrumentationt::collect(const exprt &expr)
{
  std::set<exprt> symbols;

  find_symbols(expr, symbols);

  for(std::set<exprt>::const_iterator
      s_it=symbols.begin();
      s_it!=symbols.end();
      s_it++)
  {
    if(s_it->id()==ID_symbol)
    {
      const irep_idt identifier=
        to_symbol_expr(*s_it).get_identifier();

      namespacet ns(symbol_table);
      const symbolt &symbol=ns.lookup(identifier);
      
      if(!symbol.is_state_var)
        continue;
      
      if(symbol.is_thread_local)
      {
        if(thread_local_vars.find(identifier)!=thread_local_vars.end())
          continue;

        thread_local_vart &thread_local_var=thread_local_vars[identifier];
        thread_local_var.type=symbol.type;
      }
      else
      {
        if(shared_vars.find(identifier)!=shared_vars.end())
          continue;

        shared_vart &shared_var=shared_vars[identifier];
        shared_var.type=symbol.type;
      }
    }
  }

}

/*******************************************************************\

Function: concurrency_instrumentationt::collect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concurrency_instrumentationt::collect(
  const goto_programt &goto_program,
  const is_threadedt &is_threaded)
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    if(is_threaded(i_it))
    {
      if(i_it->is_assign())
        collect(i_it->code);
      else if(i_it->is_assume() || i_it->is_assert() || i_it->is_goto())
        collect(i_it->guard);
      else if(i_it->is_function_call())
        collect(i_it->code);
    }
  }
}

/*******************************************************************\

Function: concurrency_instrumentationt::add_array_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concurrency_instrumentationt::add_array_symbols()
{
//  for(
}

/*******************************************************************\

Function: concurrency_instrumentationt::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concurrency_instrumentationt::instrument(
  goto_functionst &goto_functions)
{
  namespacet ns(symbol_table);
  is_threadedt is_threaded(ns, goto_functions);
  
  // this first collects all shared and thread-local variables
  forall_goto_functions(f_it, goto_functions)
    collect(f_it->second.body, is_threaded);
    
  // add array symbols
  add_array_symbols();

  // now instrument
  Forall_goto_functions(f_it, goto_functions)
    instrument(f_it->second.body, is_threaded);
}

/*******************************************************************\

Function: concurrency

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concurrency(
  value_setst &value_sets,
  class symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  concurrency_instrumentationt concurrency_instrumentation(value_sets, symbol_table);
  concurrency_instrumentation(goto_functions);
}

/*******************************************************************\

Module: Encoding for Threaded Goto Programs

Author: Daniel Kroening

Date: October 2012

\*******************************************************************/

/// \file
/// Encoding for Threaded Goto Programs

#include "concurrency.h"

#include <util/find_symbols.h>
#include <util/invariant.h>
#include <util/replace_symbol.h>
#include <util/std_expr.h>

#include <analyses/is_threaded.h>

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

  void instrument(goto_programt &goto_program);

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
    optionalt<symbol_exprt> array_symbol, w_index_symbol;
  };

  class thread_local_vart
  {
  public:
    typet type;
    optionalt<symbol_exprt> array_symbol;
  };

  typedef std::map<irep_idt, shared_vart> shared_varst;
  shared_varst shared_vars;

  typedef std::map<irep_idt, thread_local_vart> thread_local_varst;
  thread_local_varst thread_local_vars;
};

void concurrency_instrumentationt::instrument(exprt &expr)
{
  replace_symbolt replace_symbol;

  for(const symbol_exprt &s : find_symbols(expr))
  {
    shared_varst::const_iterator v_it = shared_vars.find(s.get_identifier());

    if(v_it != shared_vars.end())
    {
      UNIMPLEMENTED;
      // not yet done: neither array_symbol nor w_index_symbol are actually
      // initialized anywhere
      const shared_vart &shared_var = v_it->second;
      const index_exprt new_expr(
        *shared_var.array_symbol, *shared_var.w_index_symbol);

      replace_symbol.insert(s, new_expr);
    }
  }
}

void concurrency_instrumentationt::instrument(
  goto_programt &goto_program)
{
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(it->is_assign())
    {
      instrument(it->assign_rhs_nonconst());
    }
    else if(it->is_assume() || it->is_assert() || it->is_goto())
    {
      instrument(it->condition_nonconst());
    }
    else if(it->is_function_call())
    {
      code_function_callt &code = to_code_function_call(it->code_nonconst());
      instrument(code.function());

      // instrument(code.lhs(), LHS);
      for(auto &arg : code.arguments())
        instrument(arg);
    }
  }
}

void concurrency_instrumentationt::collect(const exprt &expr)
{
  for(const auto &identifier : find_symbol_identifiers(expr))
  {
    namespacet ns(symbol_table);
    const symbolt &symbol = ns.lookup(identifier);

    if(!symbol.is_state_var)
      continue;

    if(symbol.is_thread_local)
    {
      if(thread_local_vars.find(identifier) != thread_local_vars.end())
        continue;

      thread_local_vart &thread_local_var = thread_local_vars[identifier];
      thread_local_var.type = symbol.type;
    }
    else
    {
      if(shared_vars.find(identifier) != shared_vars.end())
        continue;

      shared_vart &shared_var = shared_vars[identifier];
      shared_var.type = symbol.type;
    }
  }
}

void concurrency_instrumentationt::collect(
  const goto_programt &goto_program,
  const is_threadedt &is_threaded)
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    if(is_threaded(i_it))
      i_it->apply([this](const exprt &e) { collect(e); });
  }
}

void concurrency_instrumentationt::add_array_symbols()
{
//  for(
}

void concurrency_instrumentationt::instrument(
  goto_functionst &goto_functions)
{
  namespacet ns(symbol_table);
  is_threadedt is_threaded(goto_functions);

  // this first collects all shared and thread-local variables
  for(const auto &gf_entry : goto_functions.function_map)
    collect(gf_entry.second.body, is_threaded);

  // add array symbols
  add_array_symbols();

  // now instrument
  for(auto &gf_entry : goto_functions.function_map)
    instrument(gf_entry.second.body);
}

void concurrency(
  value_setst &value_sets,
  goto_modelt &goto_model)
{
  concurrency_instrumentationt concurrency_instrumentation(
    value_sets, goto_model.symbol_table);
  concurrency_instrumentation(goto_model.goto_functions);
}

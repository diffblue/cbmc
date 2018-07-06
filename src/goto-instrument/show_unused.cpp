/*******************************************************************\

Module: Show unused variables (including write only)

Author: Norbert Manthey nmanthey@iamazon.com

\*******************************************************************/

#include <cassert>
#include <iostream>

#include <util/file_util.h>
#include <util/prefix.h>

#include <analyses/dirty.h>
#include <goto-instrument/rw_set.h>
#include <pointer-analysis/value_set_analysis_fi.h>

#include "show_unused.h"

/*******************************************************************\

Function: show_unused

  Inputs: symbol table, goto program

 Outputs: prints list of variables that are never read
          returns false, if no unused variables have been found,
          else true

 Purpose: help to spot variables that are never used globally in a
          program

\*******************************************************************/

bool show_unused(ui_message_handlert::uit ui, const goto_modelt &goto_model)
{
  const symbol_tablet &symbol_table = goto_model.symbol_table;
  const goto_functionst &goto_functions = goto_model.goto_functions;
  const namespacet ns(symbol_table);
  rw_set_baset global_reads(ns);

  // get all symbols whose address is used
  dirtyt dirty_symbols(goto_functions);

  // compute for each function the set of read and written symbols
  forall_goto_functions(it, goto_functions)
  {
    if(!it->second.body_available())
      continue;

    if(!symbol_table.has_symbol(it->first))
    {
      std::cerr << " warning: did not find symbol for: " << id2string(it->first)
                << std::endl;
      continue;
    }
    const symbolt *symbol = symbol_table.lookup(it->first);

    value_set_analysis_fit value_sets(ns);
    rw_set_functiont rw_set(value_sets, goto_model, symbol->symbol_expr());
    global_reads += rw_set;
  }

  // check the symbol table against the global_reads set, collect unused symbols
  std::vector<std::pair<const irep_idt, symbolt>> actual_unused_symbols;
  // forall_symbols(it, symbol_table.symbols)
  for(const auto symbol_pair : symbol_table.symbols)
  {
    // we are not interested in functions that are not read
    if(symbol_pair.second.type.id() == ID_code)
      continue;

    // skip internal, anonymous symbols, and if no location is present
    if(has_prefix(id2string(symbol_pair.second.name), "__CPROVER"))
      continue;
    if(has_prefix(id2string(symbol_pair.second.base_name), "#anon"))
      continue;
    if(symbol_pair.second.location.as_string().empty())
      continue;

    if(
      !global_reads.has_r_entry(symbol_pair.second.name) &&
      dirty_symbols.get_dirty_ids().find(symbol_pair.second.name) ==
        dirty_symbols.get_dirty_ids().end())
    {
      actual_unused_symbols.push_back(symbol_pair);
    }
  }

  // print collected symbols
  switch(ui)
  {
  case ui_message_handlert::uit::PLAIN:
    std::cerr << "found " << actual_unused_symbols.size()
              << " symbols to report" << std::endl;
    for(auto it = actual_unused_symbols.begin();
        it != actual_unused_symbols.end();
        ++it)
    {
      const source_locationt &location = it->second.location;
      std::cout << concat_dir_file(
                     id2string(location.get_working_directory()),
                     id2string(location.get_file()))
                << ":" << id2string(location.get_line()) << " variable "
                << id2string(it->second.base_name) << " is never read"
                << std::endl;
    }
    break;
  default:
    assert(false && "chosen UI is not yet implemented");
  }
  return 0;
}

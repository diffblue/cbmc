/*******************************************************************\

Module: Link Goto Programs

Author: Michael Tautschnig, Daniel Kroening

\*******************************************************************/

/// \file
/// Link Goto Programs

#include "link_goto_model.h"

#include <unordered_set>

#include <util/base_type.h>
#include <util/symbol.h>
#include <util/rename_symbol.h>

#include <linking/linking_class.h>
#include <util/exception_utils.h>

#include "goto_model.h"

static void rename_symbols_in_function(
  goto_functionst::goto_functiont &function,
  irep_idt &new_function_name,
  const rename_symbolt &rename_symbol)
{
  goto_programt &program=function.body;
  rename_symbol(function.type);

  Forall_goto_program_instructions(iit, program)
  {
    rename_symbol(iit->code);
    rename_symbol(iit->guard);
    // we need to update the instruction's function field as
    // well, with the new symbol for the function
    iit->function=new_function_name;
  }
}

/// Link a set of goto functions, considering weak symbols
/// and symbol renaming
static bool link_functions(
  symbol_tablet &dest_symbol_table,
  goto_functionst &dest_functions,
  const symbol_tablet &src_symbol_table,
  goto_functionst &src_functions,
  const rename_symbolt &rename_symbol,
  const std::unordered_set<irep_idt> &weak_symbols,
  const replace_symbolt &object_type_updates)
{
  namespacet ns(dest_symbol_table);
  namespacet src_ns(src_symbol_table);

  // merge functions
  Forall_goto_functions(src_it, src_functions)
  {
    // the function might have been renamed
    rename_symbolt::expr_mapt::const_iterator e_it=
      rename_symbol.expr_map.find(src_it->first);

    irep_idt final_id=src_it->first;

    if(e_it!=rename_symbol.expr_map.end())
      final_id=e_it->second;

    // already there?
    goto_functionst::function_mapt::iterator dest_f_it=
      dest_functions.function_map.find(final_id);

    goto_functionst::goto_functiont &src_func = src_it->second;
    if(dest_f_it==dest_functions.function_map.end()) // not there yet
    {
      rename_symbols_in_function(src_func, final_id, rename_symbol);
      dest_functions.function_map.emplace(final_id, std::move(src_func));
    }
    else // collision!
    {
      goto_functionst::goto_functiont &in_dest_symbol_table = dest_f_it->second;

      if(in_dest_symbol_table.body.instructions.empty() ||
         weak_symbols.find(final_id)!=weak_symbols.end())
      {
        // the one with body wins!
        rename_symbols_in_function(src_func, final_id, rename_symbol);

        in_dest_symbol_table.body.swap(src_func.body);
        in_dest_symbol_table.type=src_func.type;
      }
      else if(src_func.body.instructions.empty() ||
              src_ns.lookup(src_it->first).is_weak)
      {
        // just keep the old one in dest
      }
      else if(in_dest_symbol_table.type.get_bool(ID_C_inlined))
      {
        // ok, we silently ignore
      }
      else
      {
        // the linking code will have ensured that types match
        rename_symbol(src_func.type);
        INVARIANT(base_type_eq(in_dest_symbol_table.type, src_func.type, ns),
                  "linking ensures that types match");
      }
    }
  }

  // apply macros
  rename_symbolt macro_application;

  for(const auto &symbol_pair : dest_symbol_table.symbols)
  {
    if(symbol_pair.second.is_macro && !symbol_pair.second.is_type)
    {
      const symbolt &symbol = symbol_pair.second;

      INVARIANT(symbol.value.id() == ID_symbol, "must have symbol");
      const irep_idt &id = to_symbol_expr(symbol.value).get_identifier();

      #if 0
      if(!base_type_eq(symbol.type, ns.lookup(id).type, ns))
      {
        std::cerr << symbol << '\n';
        std::cerr << ns.lookup(id) << '\n';
      }
      INVARIANT(base_type_eq(symbol.type, ns.lookup(id).type, ns),
                "type matches");
      #endif

      macro_application.insert_expr(symbol.name, id);
    }
  }

  if(!macro_application.expr_map.empty())
    Forall_goto_functions(dest_it, dest_functions)
    {
      irep_idt final_id=dest_it->first;
      rename_symbols_in_function(dest_it->second, final_id, macro_application);
    }

  if(!object_type_updates.empty())
  {
    Forall_goto_functions(dest_it, dest_functions)
      Forall_goto_program_instructions(iit, dest_it->second.body)
      {
        object_type_updates(iit->code);
        object_type_updates(iit->guard);
      }
  }

  return false;
}

void link_goto_model(
  goto_modelt &dest,
  goto_modelt &src,
  message_handlert &message_handler)
{
  std::unordered_set<irep_idt> weak_symbols;

  for(const auto &symbol_pair : dest.symbol_table.symbols)
  {
    if(symbol_pair.second.is_weak)
      weak_symbols.insert(symbol_pair.first);
  }

  linkingt linking(dest.symbol_table,
                   src.symbol_table,
                   message_handler);

  if(linking.typecheck_main())
  {
    throw invalid_source_file_exceptiont("typechecking main failed");
  }
  if(link_functions(
       dest.symbol_table,
       dest.goto_functions,
       src.symbol_table,
       src.goto_functions,
       linking.rename_symbol,
       weak_symbols,
       linking.object_type_updates))
  {
    throw invalid_source_file_exceptiont("linking failed");
  }
}

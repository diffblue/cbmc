/*******************************************************************\

Module: Link Goto Programs

Author: Michael Tautschnig, Daniel Kroening

\*******************************************************************/

/// \file
/// Link Goto Programs

#include "link_goto_model.h"

#include <unordered_set>

#include <util/symbol.h>
#include <util/rename_symbol.h>

#include <linking/linking_class.h>

#include "goto_model.h"

static void rename_symbols_in_function(
  goto_functionst::goto_functiont &function,
  irep_idt &new_function_name,
  const rename_symbolt &rename_symbol)
{
  for(auto &identifier : function.parameter_identifiers)
  {
    auto entry = rename_symbol.expr_map.find(identifier);
    if(entry != rename_symbol.expr_map.end())
      identifier = entry->second;
  }

  for(auto &instruction : function.body.instructions)
  {
    rename_symbol(instruction.code_nonconst());

    if(instruction.has_condition())
      rename_symbol(instruction.condition_nonconst());
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
  const std::unordered_set<irep_idt> &weak_symbols)
{
  namespacet ns(dest_symbol_table);
  namespacet src_ns(src_symbol_table);

  // merge functions
  for(auto &gf_entry : src_functions.function_map)
  {
    // the function might have been renamed
    rename_symbolt::expr_mapt::const_iterator e_it =
      rename_symbol.expr_map.find(gf_entry.first);

    irep_idt final_id = gf_entry.first;

    if(e_it!=rename_symbol.expr_map.end())
      final_id=e_it->second;

    // already there?
    goto_functionst::function_mapt::iterator dest_f_it=
      dest_functions.function_map.find(final_id);

    goto_functionst::goto_functiont &src_func = gf_entry.second;
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
        in_dest_symbol_table.parameter_identifiers.swap(
          src_func.parameter_identifiers);
      }
      else if(
        src_func.body.instructions.empty() ||
        src_ns.lookup(gf_entry.first).is_weak)
      {
        // just keep the old one in dest
      }
      else if(to_code_type(ns.lookup(final_id).type).get_inlined())
      {
        // ok, we silently ignore
      }
    }
  }

  return false;
}

optionalt<replace_symbolt::expr_mapt> link_goto_model(
  goto_modelt &dest,
  goto_modelt &&src,
  message_handlert &message_handler)
{
  std::unordered_set<irep_idt> weak_symbols;

  for(const auto &symbol_pair : dest.symbol_table.symbols)
  {
    if(symbol_pair.second.is_weak)
      weak_symbols.insert(symbol_pair.first);
  }

  linkingt linking(dest.symbol_table, src.symbol_table, message_handler);

  if(linking.typecheck_main())
  {
    messaget log{message_handler};
    log.error() << "typechecking main failed" << messaget::eom;
    return {};
  }

  if(link_functions(
       dest.symbol_table,
       dest.goto_functions,
       src.symbol_table,
       src.goto_functions,
       linking.rename_symbol,
       weak_symbols))
  {
    messaget log{message_handler};
    log.error() << "linking failed" << messaget::eom;
    return {};
  }

  return linking.object_type_updates.get_expr_map();
}

void finalize_linking(
  goto_modelt &dest,
  const replace_symbolt::expr_mapt &type_updates)
{
  unchecked_replace_symbolt object_type_updates;
  object_type_updates.get_expr_map().insert(
    type_updates.begin(), type_updates.end());

  goto_functionst &dest_functions = dest.goto_functions;
  symbol_tablet &dest_symbol_table = dest.symbol_table;

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
  {
    for(auto &gf_entry : dest_functions.function_map)
    {
      irep_idt final_id = gf_entry.first;
      rename_symbols_in_function(gf_entry.second, final_id, macro_application);
    }
  }

  if(!object_type_updates.empty())
  {
    for(auto &gf_entry : dest_functions.function_map)
    {
      for(auto &instruction : gf_entry.second.body.instructions)
      {
        instruction.transform([&object_type_updates](exprt expr) {
          object_type_updates(expr);
          return expr;
        });
      }
    }
  }
}

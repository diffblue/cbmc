/*******************************************************************\

Module: Library Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Library Linking

#include "link_to_library.h"

#include <linking/static_lifetime_init.h>

#include "compute_called_functions.h"
#include "goto_convert_functions.h"
#include "goto_model.h"
#include "link_goto_model.h"

/// Try to add \p missing_function from \p library to \p goto_model.
static std::pair<optionalt<replace_symbolt::expr_mapt>, bool> add_one_function(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  const std::function<void(
    const std::set<irep_idt> &,
    const symbol_tablet &,
    symbol_tablet &,
    message_handlert &)> &library,
  const irep_idt &missing_function)
{
  goto_modelt library_model;
  library(
    {missing_function},
    goto_model.symbol_table,
    library_model.symbol_table,
    message_handler);

  // convert to CFG
  if(
    library_model.symbol_table.symbols.find(missing_function) !=
    library_model.symbol_table.symbols.end())
  {
    goto_convert(
      missing_function,
      library_model.symbol_table,
      library_model.goto_functions,
      message_handler);
  }
  // We might need a function that's outside our own library, but brought in via
  // some header file included by the library. Those functions already exist in
  // goto_model.symbol_table, but haven't been converted just yet.
  else if(
    goto_model.symbol_table.symbols.find(missing_function) !=
    goto_model.symbol_table.symbols.end())
  {
    goto_convert(
      missing_function,
      goto_model.symbol_table,
      library_model.goto_functions,
      message_handler);
  }

  // check whether additional initialization may be required
  bool init_required = false;
  if(
    goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION) !=
    goto_model.goto_functions.function_map.end())
  {
    for(const auto &entry : library_model.symbol_table)
    {
      if(
        entry.second.is_static_lifetime && !entry.second.is_type &&
        !entry.second.is_macro && entry.second.type.id() != ID_code &&
        !goto_model.symbol_table.has_symbol(entry.first))
      {
        init_required = true;
        break;
      }
    }
  }

  return {
    link_goto_model(goto_model, std::move(library_model), message_handler),
    init_required};
}

/// Complete missing function definitions using the \p library.
/// \param goto_model: goto model that may contain function calls and symbols
///   with missing function bodies
/// \param message_handler: message handler to report library processing
///   problems
/// \param library: generator function that produces function definitions (in
///   the symbol table that is the third parameter) for a given set of symbol
///   names (first parameter) that have no body in the source symbol table
///   (second parameter).
void link_to_library(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  const std::function<void(
    const std::set<irep_idt> &,
    const symbol_tablet &,
    symbol_tablet &,
    message_handlert &)> &library)
{
  // this needs a fixedpoint, as library functions
  // may depend on other library functions

  std::set<irep_idt> added_functions;
  // Linking in library functions (now seeing full definitions rather than
  // forward declarations, or perhaps even cases of missing forward
  // declarations) may result in type changes to objects.
  replace_symbolt::expr_mapt object_type_updates;
  bool need_reinit = false;

  while(true)
  {
    std::unordered_set<irep_idt> called_functions =
      compute_called_functions(goto_model.goto_functions);

    bool changed = false;
    for(const auto &id : called_functions)
    {
      goto_functionst::function_mapt::const_iterator f_it =
        goto_model.goto_functions.function_map.find(id);

      if(
        f_it != goto_model.goto_functions.function_map.end() &&
        f_it->second.body_available())
      {
        // it's overridden!
      }
      else if(added_functions.find(id) != added_functions.end())
      {
        // already added
      }
      else
      {
        changed = true;
        added_functions.insert(id);

        auto one_result =
          add_one_function(goto_model, message_handler, library, id);
        auto updates_opt = one_result.first;
        need_reinit |= one_result.second;
        if(!updates_opt.has_value())
        {
          messaget log{message_handler};
          log.warning() << "Linking library function '" << id << "' failed"
                        << messaget::eom;
          continue;
        }
        object_type_updates.insert(updates_opt->begin(), updates_opt->end());
      }
    }

    // done?
    if(!changed)
      break;
  }

  if(need_reinit)
  {
    goto_model.unload(INITIALIZE_FUNCTION);
    static_lifetime_init(
      goto_model.symbol_table,
      goto_model.symbol_table.lookup_ref(INITIALIZE_FUNCTION).location);
    goto_convert(
      INITIALIZE_FUNCTION,
      goto_model.symbol_table,
      goto_model.goto_functions,
      message_handler);
    goto_model.goto_functions.update();
  }

  if(!object_type_updates.empty())
    finalize_linking(goto_model, object_type_updates);

  add_history_transform(
    goto_transform_kindt::link_to_library, goto_model.goto_functions);
}

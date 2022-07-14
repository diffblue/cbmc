/*******************************************************************\

Module: value_set_fi_Fp_removal

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "value_set_fi_fp_removal.h"

#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_function_pointers.h>

#include <pointer-analysis/value_set_analysis_fi.h>

void value_set_fi_fp_removal(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  message.status() << "Doing FI value set analysis" << messaget::eom;

  const namespacet ns(goto_model.symbol_table);
  value_set_analysis_fit value_sets(ns);
  value_sets(goto_model.goto_functions);

  message.status() << "Instrumenting" << messaget::eom;

  // now replace aliases by addresses
  for(auto &f : goto_model.goto_functions.function_map)
  {
    for(auto target = f.second.body.instructions.begin();
        target != f.second.body.instructions.end();
        target++)
    {
      if(target->is_function_call())
      {
        const auto &function = as_const(*target).call_function();
        if(function.id() == ID_dereference)
        {
          message.status() << "CALL at " << target->source_location() << ":"
                           << messaget::eom;

          const auto &pointer = to_dereference_expr(function).pointer();
          auto addresses = value_sets.get_values(f.first, target, pointer);

          std::unordered_set<symbol_exprt, irep_hash> functions;

          for(const auto &address : addresses)
          {
            // is this a plain function address?
            // strip leading '&'
            if(address.id() == ID_object_descriptor)
            {
              const auto &od = to_object_descriptor_expr(address);
              const auto &object = od.object();
              if(object.type().id() == ID_code && object.id() == ID_symbol)
                functions.insert(to_symbol_expr(object));
            }
          }

          for(const auto &f : functions)
            message.status()
              << "  function: " << f.get_identifier() << messaget::eom;

          if(functions.size() > 0)
          {
            remove_function_pointer(
              message_handler,
              goto_model.symbol_table,
              f.second.body,
              f.first,
              target,
              functions);
          }
        }
      }
    }
  }
  goto_model.goto_functions.update();
}

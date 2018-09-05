/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "value_set_fi_fp_removal.h"

#include <goto-programs/goto_model.h>

#include <pointer-analysis/value_set_analysis_fi.h>

#if 0
#include <util/std_code.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/union_find.h>
#include <util/type_eq.h>
#include <util/fresh_symbol.h>
#include <util/expanding_vector.h>
#endif

#include <iostream>

void remove_function_pointer(
  goto_programt &goto_program,
  goto_programt::targett target,
  const std::set<symbol_exprt> &functions,
  goto_modelt &goto_model);

void value_set_fi_fp_removal(goto_modelt &goto_model)
{
  std::cout << "Doing FI value set analysis\n";

  const namespacet ns(goto_model.symbol_table);
  value_set_analysis_fit value_sets(ns);
  value_sets(goto_model.goto_functions);

  std::cout << "Instrumenting\n";
  
  // now replace aliases by addresses
  for(auto & f : goto_model.goto_functions.function_map)
  {
    for(auto target=f.second.body.instructions.begin();
        target!=f.second.body.instructions.end();
        target++)
    {
      if(target->is_function_call())
      {
        const auto &call=to_code_function_call(target->code);
        if(call.function().id()==ID_dereference)
        {
          std::cout << "CALL at " << target->source_location << ":\n";

          const auto &pointer=to_dereference_expr(call.function()).pointer();
          std::list<exprt> addresses;
          value_sets.get_values(target, pointer, addresses);

          std::set<symbol_exprt> functions;

          for(const auto &address : addresses)
          {
            // is this a plain function address?
            // strip leading '&'
            if(address.id()==ID_unknown)
            {
              // uh
            }
            else if(address.id()==ID_object_descriptor)
            {
              const auto &od=to_object_descriptor_expr(address);
              const auto &object=od.object();
              if(object.type().id()==ID_code &&
                 object.id()==ID_symbol)
                functions.insert(to_symbol_expr(object));
            }
          }

          for(const auto &f : functions)
            std::cout << "  function: " << f.get_identifier() << '\n';

          remove_function_pointer(
            f.second.body, target, functions, goto_model);
        }
      }
    }
  }

  goto_model.goto_functions.update();
}

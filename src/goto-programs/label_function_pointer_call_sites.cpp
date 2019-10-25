/*******************************************************************\
Module: Label function pointer call sites
Author: Diffblue Ltd.
\*******************************************************************/

/// \file
/// Label function pointer call sites across a goto model

#include "label_function_pointer_call_sites.h"

#include <util/fresh_symbol.h>

void label_function_pointer_call_sites(goto_modelt &goto_model)
{
  for(auto &goto_function : goto_model.goto_functions.function_map)
  {
    std::size_t function_pointer_call_counter = 0;
    for_each_goto_location_if(
      goto_function.second,
      [](const goto_programt::targett it) {
        return it->is_function_call() && can_cast_expr<dereference_exprt>(
                                           it->get_function_call().function());
      },
      [&](goto_programt::targett it) {
        auto const &function_call = it->get_function_call();
        auto const &function_pointer_dereference =
          to_dereference_expr(function_call.function());
        auto const &source_location = function_call.source_location();
        auto const &goto_function_symbol_mode =
          goto_model.symbol_table.lookup_ref(goto_function.first).mode;
        auto const new_symbol_name =
          irep_idt{id2string(goto_function.first) + ".function_pointer_call." +
                   std::to_string(++function_pointer_call_counter)};
        goto_model.symbol_table.insert([&] {
          symbolt function_call_site_symbol{};
          function_call_site_symbol.name = function_call_site_symbol.base_name =
            function_call_site_symbol.pretty_name = new_symbol_name;
          function_call_site_symbol.type =
            function_pointer_dereference.pointer().type();
          function_call_site_symbol.location = function_call.source_location();
          function_call_site_symbol.is_lvalue = true;
          function_call_site_symbol.mode = goto_function_symbol_mode;
          return function_call_site_symbol;
        }());
        auto const new_function_pointer =
          goto_model.symbol_table.lookup_ref(new_symbol_name).symbol_expr();
        auto const assign_instruction = goto_programt::make_assignment(
          code_assignt{new_function_pointer,
                       function_pointer_dereference.pointer()},
          source_location);
        goto_function.second.body.insert_before(it, assign_instruction);
        to_code_function_call(it->code).function() =
          dereference_exprt{new_function_pointer};
      });
  }
}

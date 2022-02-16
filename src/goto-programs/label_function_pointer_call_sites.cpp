/*******************************************************************\
Module: Label function pointer call sites
Author: Diffblue Ltd.
\*******************************************************************/

/// \file
/// Label function pointer call sites across a goto model

#include "label_function_pointer_call_sites.h"

#include <util/pointer_expr.h>

#include "goto_model.h"

void label_function_pointer_call_sites(goto_modelt &goto_model)
{
  for(auto &goto_function : goto_model.goto_functions.function_map)
  {
    std::size_t function_pointer_call_counter = 0;

    for_each_instruction_if(
      goto_function.second,
      [](const goto_programt::targett it) {
        return it->is_function_call() &&
               can_cast_expr<dereference_exprt>(it->call_function());
      },
      [&](goto_programt::targett &it) {
        auto const &function_pointer_dereference =
          to_dereference_expr(it->call_function());
        auto const &source_location = it->source_location();
        auto const &goto_function_symbol_mode =
          goto_model.symbol_table.lookup_ref(goto_function.first).mode;

        auto const call_site_symbol_name =
          irep_idt{id2string(goto_function.first) + ".function_pointer_call." +
                   std::to_string(++function_pointer_call_counter)};

        // insert new function pointer variable into the symbol table
        goto_model.symbol_table.insert([&] {
          symbolt function_call_site_symbol{};
          function_call_site_symbol.name = function_call_site_symbol.base_name =
            function_call_site_symbol.pretty_name = call_site_symbol_name;
          function_call_site_symbol.type =
            function_pointer_dereference.pointer().type();
          function_call_site_symbol.location = it->source_location();
          function_call_site_symbol.is_lvalue = true;
          function_call_site_symbol.mode = goto_function_symbol_mode;
          return function_call_site_symbol;
        }());

        auto const new_function_pointer =
          goto_model.symbol_table.lookup_ref(call_site_symbol_name)
            .symbol_expr();

        // add a DECL instruction for the function pointer variable
        auto decl_instruction =
          goto_programt::make_decl(new_function_pointer, source_location);

        goto_function.second.body.insert_before_swap(it, decl_instruction);
        ++it;

        // add assignment to the new variable
        auto assign_instruction = goto_programt::make_assignment(
          code_assignt{new_function_pointer,
                       function_pointer_dereference.pointer()},
          source_location);

        goto_function.second.body.insert_before_swap(it, assign_instruction);
        ++it;

        // transform original call into a call to the new variable
        it->call_function() = dereference_exprt{new_function_pointer};
        ++it;

        // add a DEAD instruction for the new variable
        auto dead_instruction =
          goto_programt::make_dead(new_function_pointer, source_location);
        goto_function.second.body.insert_before_swap(it, dead_instruction);
        // the iterator now points to the DEAD instruction and will be
        // incremented by the outer loop
      });
  }
}

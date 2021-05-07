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
        return it->is_function_call() && can_cast_expr<dereference_exprt>(
                                           it->get_function_call().function());
      },
      [&](goto_programt::targett &it) {
        auto const &function_call = it->get_function_call();
        auto const &function_pointer_dereference =
          to_dereference_expr(function_call.function());
        auto const &source_location = function_call.source_location();
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
          function_call_site_symbol.location = function_call.source_location();
          function_call_site_symbol.is_lvalue = true;
          function_call_site_symbol.mode = goto_function_symbol_mode;
          return function_call_site_symbol;
        }());

        auto const new_function_pointer =
          goto_model.symbol_table.lookup_ref(call_site_symbol_name)
            .symbol_expr();

        // add assignment to the new function pointer variable, followed by a
        // call of the new variable
        auto assign_instruction = goto_programt::make_assignment(
          code_assignt{new_function_pointer,
                       function_pointer_dereference.pointer()},
          source_location);

        goto_function.second.body.insert_before_swap(it, assign_instruction);
        const auto next = std::next(it);
        to_code_function_call(next->code_nonconst()).function() =
          dereference_exprt{new_function_pointer};
        // we need to increment the iterator once more (in addition to the
        // increment already done by for_each_goto_function_if()). This is
        // because insert_before_swap() inserts a new instruction after the
        // instruction pointed to by it (and then swaps the contents with the
        // previous instruction). We need to increment the iterator as we also
        // need to skip over this newly inserted instruction.
        it++;
      });
  }
}

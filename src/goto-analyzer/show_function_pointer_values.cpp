// Module: Show function pointer values
// Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com
// Copyright: Diffblue Ltd, 2020

#include "show_function_pointer_values.h"

#include <util/message.h>
#include <util/namespace.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/restrict_function_pointers.h>

#include <analyses/ai.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>

#include <regex>
#include <string>

void print_function_pointer_values(
    const goto_modelt &goto_model,
    const ai_baset &ai,
    const optionst &options,
    message_handlert &message_handler,
    std::string filename)
{
    function_pointer_restrictionst::restrictionst map;
    namespacet ns(goto_model.symbol_table);

    messaget m(message_handler);
    m.status() << "Getting function pointer targets at specific callsites" << messaget::eom;

    for(auto const &function_entry :  goto_model.goto_functions.function_map)
    {
        for_each_goto_location(function_entry.second, [&](ai_baset::locationt instruction_location)
        {
            auto is_assign = instruction_location->is_assign();
            if (is_assign)
            {
                auto assign_stmt = instruction_location->get_assign();
                auto lhs = assign_stmt.lhs();
                std::string identifier =
                    id2string(to_symbol_expr(lhs).get_identifier());
                // <name of function>.function_pointer_call.<integer>
                std::regex name(R"(\w+\.function_pointer_call\.\d+)");
                if (std::regex_match(identifier, name)) {
                    auto const state_after_unique_ptr = ai.abstract_state_after(instruction_location);
                    PRECONDITION(state_after_unique_ptr != nullptr);
                    auto state_after = 
                        dynamic_cast<variable_sensitivity_domaint *>(
                        state_after_unique_ptr.get());
                    CHECK_RETURN(state_after != nullptr);
                    auto const lhs_identifier = to_symbol_expr(lhs).get_identifier();
                    
                    if (state_after->is_top())
                    {
                        // for top, we don't add restrictions (i.e. normal function pointer removal should take care of this).
                    }
                    else if (state_after->is_bottom())
                    {
                        // call site is unreachable, so this is empty set
                        map[lhs_identifier] = {};
                    }
                    else
                    {
                        auto evaluated_object =
                            state_after->eval(lhs, ns).get();
                        auto value_set_object =
                            (value_set_abstract_objectt *) evaluated_object;
                        auto values = value_set_object->get_values();                 
                        auto get_function_pointer_name = [](const exprt &function_pointer) {
                            return to_symbol_expr(to_address_of_expr(function_pointer).op()).get_identifier();
                        };
                
                        for (const auto &elem : values)
                        {
                            map[lhs_identifier].insert(get_function_pointer_name(elem));
                        }
                    }
                }
            }
        });
    }
    function_pointer_restrictionst{std::move(map)}.write_to_file(filename);
}
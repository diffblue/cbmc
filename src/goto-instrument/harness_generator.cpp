/*******************************************************************\

Module: Harness generator

Author: elizabeth.polgreen@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// harness generator


#include "harness_generator.h"

#include <util/std_types.h>
#include <util/message.h>

#include <langapi/language_util.h>


void harness_generatort::build_harness
(const goto_modelt & goto_model,
    irep_idt function,
    message_handlert &message_handler)
{
  namespacet ns(goto_model.symbol_table);

  messaget message(message_handler);
  value_set_analysist value_set_analysis(ns);
  value_set_analysis(goto_model.goto_functions);

  auto f_it = goto_model.goto_functions.function_map.find(function);
  if(f_it == goto_model.goto_functions.function_map.end())
  {
    message.error() << "failed to find function "<< function << messaget::eom;
    return;
  }

  if(f_it ->second.body.instructions.empty())
  {
    message.error() << "function " << function
                    << " has no body " << messaget::eom;
  }

  value_set_domaint domain = value_set_analysis
      [f_it->second.body.instructions.begin()];

  code_typet::parameterst parameters = f_it->second.type.parameters();

  for(const auto &p : parameters)
  {
    value_setst::valuest parameter_values;
    symbol_exprt expression(p.get_identifier(), p.type());
    domain.value_set.get_value_set(expression, parameter_values, ns);

    for(const auto &v : parameter_values)
     {
       if(v.id()==ID_object_descriptor)
       {
         const auto &o=to_object_descriptor_expr(v);

         message.result() << "parameter " << p.get_identifier() << ": "
                          << from_expr(ns, p.get_identifier(), o.object())
                          << messaget::eom;
       }
     }
  }
}

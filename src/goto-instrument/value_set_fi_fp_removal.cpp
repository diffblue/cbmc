/*******************************************************************\

Module: value_set_fi_Fp_removal

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "value_set_fi_fp_removal.h"

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_function_pointers.h>

#include <pointer-analysis/value_set_analysis_fi.h>

#include <util/base_type.h>
#include <util/c_types.h>
#include <util/expanding_vector.h>
#include <util/fresh_symbol.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/union_find.h>

#ifdef USE_STD_STRING
#  include <util/dstring.h>
#endif

void fix_argument_types(
  code_function_callt &function_call,
  const namespacet &ns)
{
  const code_typet &code_type =
    to_code_type(ns.follow(function_call.function().type()));

  const code_typet::parameterst &function_parameters = code_type.parameters();

  code_function_callt::argumentst &call_arguments = function_call.arguments();

  for(std::size_t i = 0; i < function_parameters.size(); i++)
  {
    // casting pointers might result in more arguments than function parameters
    if(i < call_arguments.size())
    {
      call_arguments[i] = typecast_exprt::conditional_cast(
        call_arguments[i], function_parameters[i].type());
    }
  }
}

void fix_return_type(
  code_function_callt &function_call,
  goto_programt &dest,
  goto_modelt &goto_model)
{
  // are we returning anything at all?
  if(function_call.lhs().is_nil())
    return;

  const namespacet ns(goto_model.symbol_table);

  const code_typet &code_type =
    to_code_type(ns.follow(function_call.function().type()));

  // type already ok?
  if(function_call.lhs().type() == code_type.return_type())
    return;

  const symbolt &function_symbol =
    ns.lookup(to_symbol_expr(function_call.function()).get_identifier());

  symbolt &tmp_symbol = get_fresh_aux_symbol(
    code_type.return_type(),
    id2string(function_call.source_location().get_function()),
    "tmp_return_val_" + id2string(function_symbol.base_name),
    function_call.source_location(),
    function_symbol.mode,
    goto_model.symbol_table);

  const symbol_exprt tmp_symbol_expr = tmp_symbol.symbol_expr();

  exprt old_lhs = function_call.lhs();
  function_call.lhs() = tmp_symbol_expr;

  dest.add(goto_programt::make_assignment(
    code_assignt(old_lhs, typecast_exprt(tmp_symbol_expr, old_lhs.type()))));
}

void remove_function_pointer(
  goto_programt &goto_program,
  goto_programt::targett target,
  const std::set<symbol_exprt> &functions,
  goto_modelt &goto_model)
{
  const code_function_callt &code = to_code_function_call(target->code);

  const exprt &function = code.function();
  PRECONDITION(function.id() == ID_dereference);

  // this better have the right type
  code_typet call_type = to_code_type(function.type());

  // refine the type in case the forward declaration was incomplete
  if(call_type.has_ellipsis() && call_type.parameters().empty())
  {
    call_type.remove_ellipsis();
    forall_expr(it, code.arguments())
      call_type.parameters().push_back(code_typet::parametert(it->type()));
  }

  const exprt &pointer = to_dereference_expr(function).pointer();

  // the final target is a skip
  goto_programt final_skip;

  goto_programt::targett t_final = final_skip.add_instruction();
  t_final->make_skip();

  // build the calls and gotos

  goto_programt new_code_calls;
  goto_programt new_code_gotos;

  for(const auto &fun : functions)
  {
    // call function
    goto_programt::targett t1 = new_code_calls.add_instruction();
    t1->make_function_call(code);
    to_code_function_call(t1->code).function() = fun;

    // the signature of the function might not match precisely
    const namespacet ns(goto_model.symbol_table);
    fix_argument_types(to_code_function_call(t1->code), ns);
    fix_return_type(
      to_code_function_call(t1->code), new_code_calls, goto_model);

    // goto final
    goto_programt::targett t3 = new_code_calls.add_instruction();
    t3->make_goto(t_final, true_exprt());

    // goto to call
    address_of_exprt address_of(fun, pointer_type(fun.type()));

    goto_programt::targett t4 = new_code_gotos.add_instruction();
    t4->make_goto(
      t1,
      equal_exprt(
        pointer, typecast_exprt::conditional_cast(address_of, pointer.type())));
  }

  goto_programt::targett t = new_code_gotos.add_instruction();
  t->make_assertion(false_exprt());
  t->source_location.set_property_class("pointer dereference");
  t->source_location.set_comment("invalid function pointer");

  goto_programt new_code;

  // patch them all together
  new_code.destructive_append(new_code_gotos);
  new_code.destructive_append(new_code_calls);
  new_code.destructive_append(final_skip);

  // set locations
  for(auto &instruction : new_code.instructions)
  {
    irep_idt property_class = instruction.source_location.get_property_class();
    irep_idt comment = instruction.source_location.get_comment();
    instruction.source_location = target->source_location;
    if(!property_class.empty())
      instruction.source_location.set_property_class(property_class);
    if(!comment.empty())
      instruction.source_location.set_comment(comment);
  }

  goto_programt::targett next_target = target;
  next_target++;

  goto_program.destructive_insert(next_target, new_code);

  // We preserve the original dereferencing to possibly catch
  // further pointer-related errors.
  code_expressiont code_expression(function);
  code_expression.add_source_location() = function.source_location();
  target->code.swap(code_expression);
  target->type = OTHER;
}

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
        const auto &call = to_code_function_call(target->code);
        if(call.function().id() == ID_dereference)
        {
          message.status() << "CALL at " << target->source_location << ":"
                           << messaget::eom;

          const auto &pointer = to_dereference_expr(call.function()).pointer();
          std::list<exprt> addresses;
          value_sets.get_values(f.first, target, pointer, addresses);

          std::set<symbol_exprt> functions;

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
            remove_function_pointer(
              f.second.body, target, functions, goto_model);
        }
      }
    }
  }
  goto_model.goto_functions.update();
}

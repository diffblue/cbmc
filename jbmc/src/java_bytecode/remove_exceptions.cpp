/*******************************************************************\

Module: Remove exception handling

Author: Cristina David

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove exception handling (Java): the language-specific hooks of the shared
/// remove_exceptions_baset lowering.  Java exceptions are Throwable references
/// (an @inflight_exception pointer global), matched with java_instanceof, and
/// bound at code_landingpadt instructions.

#include "remove_exceptions.h"

#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_exceptions_base.h>

#include <analyses/uncaught_exceptions_analysis.h>

#include "java_expr.h"
#include "java_types.h"
#include "remove_instanceof.h"

/// Java specialization of the shared exception-lowering base.  Exceptions are
/// Throwable references carried in the @inflight_exception global; handlers are
/// matched with java_instanceof (optionally lowered to a @class_identifier
/// check) and bound at code_landingpadt instructions.
class remove_exceptionst : public remove_exceptions_baset
{
public:
  remove_exceptionst(
    symbol_table_baset &_symbol_table,
    const class_hierarchyt *_class_hierarchy,
    function_may_throwt _function_may_throw,
    bool _remove_added_instanceof,
    message_handlert &_message_handler)
    : remove_exceptions_baset(
        _symbol_table,
        std::move(_function_may_throw),
        _message_handler),
      class_hierarchy(_class_hierarchy),
      remove_added_instanceof(_remove_added_instanceof)
  {
    if(remove_added_instanceof)
    {
      INVARIANT(
        class_hierarchy != nullptr,
        "remove_exceptions needs a class hierarchy to remove instanceof "
        "statements (either supply one, or don't use REMOVE_ADDED_INSTANCEOF)");
    }
  }

protected:
  const class_hierarchyt *class_hierarchy;
  bool remove_added_instanceof;

  symbol_exprt get_inflight_exception_global() override;

  exprt no_inflight_exception() override;

  void add_handler_dispatch(
    const irep_idt &function_identifier,
    goto_programt &goto_program,
    const goto_programt::targett &instr_it,
    const irep_idt &tag,
    const goto_programt::targett &handler_target) override;

  void set_inflight_exception(
    goto_programt &goto_program,
    const goto_programt::targett &instr_it) override;

  void instrument_exception_handler(
    goto_programt &goto_program,
    const goto_programt::targett &instr_it,
    bool may_catch) override;
};

/// Returns the the global @inflight_exception, holding a reference to an
/// exception that has been thrown but not yet caught.
symbol_exprt remove_exceptionst::get_inflight_exception_global()
{
  const symbolt *existing_symbol =
    symbol_table.lookup(INFLIGHT_EXCEPTION_VARIABLE_NAME);
  INVARIANT(
    existing_symbol != nullptr,
    "Java frontend should have created @inflight_exception variable");
  return existing_symbol->symbol_expr();
}

exprt remove_exceptionst::no_inflight_exception()
{
  return equal_exprt(
    get_inflight_exception_global(),
    null_pointer_exprt(pointer_type(java_void_type())));
}

void remove_exceptionst::add_handler_dispatch(
  const irep_idt &function_identifier,
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const irep_idt &tag,
  const goto_programt::targett &handler_target)
{
  // use instanceof to check that this is the correct handler
  struct_tag_typet type(tag);
  java_instanceof_exprt check(get_inflight_exception_global(), type);

  goto_programt::targett t_exc = goto_program.insert_after(
    instr_it,
    goto_programt::make_goto(
      handler_target, check, instr_it->source_location()));

  if(remove_added_instanceof)
  {
    remove_instanceof(
      function_identifier,
      t_exc,
      goto_program,
      symbol_table,
      *class_hierarchy,
      message_handler);
  }
}

void remove_exceptionst::set_inflight_exception(
  goto_programt &goto_program,
  const goto_programt::targett &instr_it)
{
  (void)goto_program;
  const exprt &exc_expr =
    uncaught_exceptions_domaint::get_exception_symbol(instr_it->code());

  const symbol_exprt exc_thrown = get_inflight_exception_global();

  // turn the `throw' into an assignment with the appropriate cast
  *instr_it = goto_programt::make_assignment(
    exc_thrown,
    typecast_exprt(exc_expr, exc_thrown.type()),
    instr_it->source_location());
}

/// Translates an exception landing-pad into instructions that copy the
/// in-flight exception pointer to a nominated expression, then clear the
/// in-flight exception (i.e. null the pointer), hence marking it caught.
void remove_exceptionst::instrument_exception_handler(
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  bool may_catch)
{
  PRECONDITION(instr_it->type() == CATCH);

  if(may_catch)
  {
    // retrieve the exception variable
    const exprt &thrown_exception_local =
      to_code_landingpad(instr_it->code()).catch_expr();

    const symbol_exprt thrown_global_symbol = get_inflight_exception_global();
    // next we reset the exceptional return to NULL
    null_pointer_exprt null_voidptr((pointer_type(java_void_type())));

    // add the assignment @inflight_exception = NULL
    goto_program.insert_after(
      instr_it,
      goto_programt::make_assignment(
        code_assignt(thrown_global_symbol, null_voidptr),
        instr_it->source_location()));

    // add the assignment exc = @inflight_exception (before the null assignment)
    goto_program.insert_after(
      instr_it,
      goto_programt::make_assignment(
        code_assignt(
          thrown_exception_local,
          typecast_exprt(thrown_global_symbol, thrown_exception_local.type())),
        instr_it->source_location()));
  }

  instr_it->turn_into_skip();
}

/// removes throws/CATCH-POP/CATCH-PUSH
void remove_exceptions_using_instanceof(
  symbol_table_baset &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  const namespacet ns(symbol_table);
  std::map<irep_idt, std::set<irep_idt>> exceptions_map;

  uncaught_exceptions(goto_functions, ns, exceptions_map);

  remove_exceptionst::function_may_throwt function_may_throw =
    [&exceptions_map](const irep_idt &id)
  { return !exceptions_map[id].empty(); };

  remove_exceptionst remove_exceptions(
    symbol_table, nullptr, function_may_throw, false, message_handler);

  remove_exceptions(goto_functions);
}

/// removes throws/CATCH-POP/CATCH-PUSH from a single GOTO program, replacing
/// them with explicit exception propagation.
void remove_exceptions_using_instanceof(
  const irep_idt &function_identifier,
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  remove_exceptionst::function_may_throwt any_function_may_throw =
    [](const irep_idt &) { return true; };

  remove_exceptionst remove_exceptions(
    symbol_table, nullptr, any_function_may_throw, false, message_handler);

  remove_exceptions(function_identifier, goto_program);
}

/// removes throws/CATCH-POP/CATCH-PUSH, replacing them with explicit exception
/// propagation.
void remove_exceptions_using_instanceof(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  remove_exceptions_using_instanceof(
    goto_model.symbol_table, goto_model.goto_functions, message_handler);
}

/// removes throws/CATCH-POP/CATCH-PUSH
void remove_exceptions(
  symbol_table_baset &symbol_table,
  goto_functionst &goto_functions,
  const class_hierarchyt &class_hierarchy,
  message_handlert &message_handler)
{
  const namespacet ns(symbol_table);
  std::map<irep_idt, std::set<irep_idt>> exceptions_map;

  uncaught_exceptions(goto_functions, ns, exceptions_map);

  remove_exceptionst::function_may_throwt function_may_throw =
    [&exceptions_map](const irep_idt &id)
  { return !exceptions_map[id].empty(); };

  remove_exceptionst remove_exceptions(
    symbol_table, &class_hierarchy, function_may_throw, true, message_handler);

  remove_exceptions(goto_functions);
}

/// removes throws/CATCH-POP/CATCH-PUSH from a single GOTO program, replacing
/// them with explicit exception propagation.
void remove_exceptions(
  const irep_idt &function_identifier,
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  const class_hierarchyt &class_hierarchy,
  message_handlert &message_handler)
{
  remove_exceptionst::function_may_throwt any_function_may_throw =
    [](const irep_idt &) { return true; };

  remove_exceptionst remove_exceptions(
    symbol_table,
    &class_hierarchy,
    any_function_may_throw,
    true,
    message_handler);

  remove_exceptions(function_identifier, goto_program);
}

/// removes throws/CATCH-POP/CATCH-PUSH, replacing them with explicit exception
/// propagation.
void remove_exceptions(
  goto_modelt &goto_model,
  const class_hierarchyt &class_hierarchy,
  message_handlert &message_handler)
{
  remove_exceptions(
    goto_model.symbol_table,
    goto_model.goto_functions,
    class_hierarchy,
    message_handler);
}

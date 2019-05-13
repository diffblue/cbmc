/*******************************************************************\

Module: Remove function return values

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

/// \file
/// Replace function returns by assignments to global variables

#include "remove_returns.h"

#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/fresh_symbol.h>
#include <util/std_expr.h>
#include <util/suffix.h>

#include "goto_model.h"

#include "collect_function_pointer_targets.h"
#include "remove_function_pointers.h"
#include "remove_skip.h"

#define RETURN_VALUE_SUFFIX "#return_value"

class remove_returnst
{
public:
  explicit remove_returnst(
    symbol_table_baset &_symbol_table,
    message_handlert &m)
    : log(m), symbol_table(_symbol_table)
  {
  }

  void operator()(
    goto_functionst &goto_functions);

  void operator()(
    goto_model_functiont &model_function,
    function_is_stubt function_is_stub);

  void restore(
    goto_functionst &goto_functions);

  /// Build the internal map to know the potential function pointer targets
  /// \param goto_model: The model to search for the targets
  void build_fp_targets(goto_modelt &goto_model)
  {
    possible_fp_targets_map = get_function_pointer_targets(
      log.get_message_handler(),
      goto_model.goto_functions,
      goto_model.symbol_table);
  }

protected:
  messaget log;
  symbol_table_baset &symbol_table;
  possible_fp_targets_mapt possible_fp_targets_map;

  void replace_returns(
    const irep_idt &function_id,
    goto_functionst::goto_functiont &function);

  bool do_function_calls(
    function_is_stubt function_is_stub,
    goto_programt &goto_program);

  bool restore_returns(
    goto_functionst::function_mapt::iterator f_it);

  void undo_function_calls(
    goto_programt &goto_program);

  optionalt<symbol_exprt>
  get_or_create_return_value_symbol(const irep_idt &function_id);

  /// Remove return of a complete function call
  /// \param target: the function call instruction iterator
  /// \param goto_program: the GOTO program to be updated
  void do_function_call_complete(
    goto_programt::targett target,
    goto_programt &goto_program);

  /// Remove return of a complete function call of a function pointer
  /// \param target: the function call instruction iterator
  /// \param possible_fp_targets: functions the pointer may point to
  /// \param goto_program: the GOTO program to be updated
  void do_function_call_complete(
    goto_programt::targett target,
    const possible_fp_targetst &possible_fp_targets,
    goto_programt &goto_program);

  /// Remove return of a stub function call
  /// \param target: the function call instruction iterator
  /// \param goto_program: the GOTO program to be updated
  void do_function_call_stub(
    goto_programt::targett target,
    goto_programt &goto_program);
};

optionalt<symbol_exprt>
remove_returnst::get_or_create_return_value_symbol(const irep_idt &function_id)
{
  const namespacet ns(symbol_table);
  const auto symbol_expr = return_value_symbol(function_id, ns);
  const auto symbol_name = symbol_expr.get_identifier();
  if(symbol_table.has_symbol(symbol_name))
    return symbol_expr;

  const symbolt &function_symbol = symbol_table.lookup_ref(function_id);
  const typet &return_type = to_code_type(function_symbol.type).return_type();

  if(return_type == empty_typet())
    return {};

  auxiliary_symbolt new_symbol;
  new_symbol.is_static_lifetime = true;
  new_symbol.module = function_symbol.module;
  new_symbol.base_name =
    id2string(function_symbol.base_name) + RETURN_VALUE_SUFFIX;
  new_symbol.name = symbol_name;
  new_symbol.mode = function_symbol.mode;
  // If we're creating this for the first time, the target function cannot have
  // been remove_return'd yet, so this will still be the "true" return type:
  new_symbol.type = return_type;
  // Return-value symbols will always be written before they are read, so there
  // is no need for __CPROVER_initialize to do anything:
  new_symbol.type.set(ID_C_no_initialization_required, true);

  symbol_table.add(new_symbol);
  return new_symbol.symbol_expr();
}

/// turns 'return x' into an assignment to fkt#return_value
/// \param function_id: name of the function to transform
/// \param function: function to transform
void remove_returnst::replace_returns(
  const irep_idt &function_id,
  goto_functionst::goto_functiont &function)
{
  typet return_type = function.type.return_type();

  // returns something but void?
  if(return_type == empty_typet())
    return;

  // add return_value symbol to symbol_table, if not already created:
  const auto return_symbol = get_or_create_return_value_symbol(function_id);

  goto_programt &goto_program = function.body;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_return())
    {
      INVARIANT(
        i_it->code.operands().size() == 1,
        "return instructions should have one operand");

      if(return_symbol.has_value())
      {
        // replace "return x;" by "fkt#return_value=x;"
        code_assignt assignment(*return_symbol, i_it->code.op0());

        // now turn the `return' into `assignment'
        *i_it =
          goto_programt::make_assignment(assignment, i_it->source_location);
      }
      else
        i_it->turn_into_skip();
    }
  }
}

/// turns x=f(...) into f(...); lhs=f#return_value;
/// \param function_is_stub: function (irep_idt -> bool) that determines whether
///   a given function ID is a stub
/// \param goto_program: program to transform
/// \return True if, and only if, instructions have been inserted. In that case
///   the caller must invoke an appropriate method to update location numbers.
bool remove_returnst::do_function_calls(
  function_is_stubt function_is_stub,
  goto_programt &goto_program)
{
  bool requires_update = false;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(!i_it->is_function_call())
      continue;

    code_function_callt function_call = i_it->get_function_call();

    INVARIANT(
      function_call.function().id() == ID_symbol ||
        function_call.function().id() == ID_dereference,
      "only direct function calls (via a symbol) or indirect function calls "
      "(via a dereference) are supported");

    bool is_function_pointer = function_call.function().id() == ID_dereference;

    const auto &function_symbol =
      is_function_pointer
        ? to_dereference_expr(function_call.function()).pointer()
        : function_call.function();
    const auto &function_id = to_symbol_expr(function_symbol).get_identifier();

    // Do we return anything?
    if(
      to_code_type(function_call.function().type()).return_type() ==
        empty_typet() ||
      !function_call.lhs().is_not_nil())
      continue;

    if(is_function_pointer)
    {
      // f may point to {f1,f2,..}=possible_fp_targets_map[function_id]
      // lhs=*f(..) => *f(..); lhs = (f == f1 ? f1#return_value : f == f2 ? ..);
      do_function_call_complete(
        i_it, possible_fp_targets_map[function_id].second, goto_program);
    }
    else if(function_is_stub(function_id))
    {
      // stub:
      // lhs=f(..) => f(..); lhs=nondet;
      do_function_call_stub(i_it, goto_program);
    }
    else
    {
      // lhs=f(..) => f(..); lhs=f#return_value;
      do_function_call_complete(i_it, goto_program);
    }

    // fry the previous assignment
    function_call.lhs().make_nil();

    // update the call
    i_it->set_function_call(function_call);

    requires_update = true;
  }
  return requires_update;
}

void remove_returnst::operator()(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
  {
    // NOLINTNEXTLINE
    auto function_is_stub = [&goto_functions](const irep_idt &function_id) {
      auto findit = goto_functions.function_map.find(function_id);
      INVARIANT(
        findit != goto_functions.function_map.end(),
        "called function should have some entry in the function map");
      return !findit->second.body_available();
    };

    replace_returns(it->first, it->second);
    if(do_function_calls(function_is_stub, it->second.body))
      goto_functions.compute_location_numbers(it->second.body);
  }
}

void remove_returnst::operator()(
  goto_model_functiont &model_function,
  function_is_stubt function_is_stub)
{
  goto_functionst::goto_functiont &goto_function =
    model_function.get_goto_function();

  // If this is a stub it doesn't have a corresponding #return_value,
  // not any return instructions to alter:
  if(goto_function.body.empty())
    return;

  replace_returns(model_function.get_function_id(), goto_function);
  if(do_function_calls(function_is_stub, goto_function.body))
    model_function.compute_location_numbers();
}

/// removes returns
void remove_returns(
  symbol_table_baset &symbol_table,
  message_handlert &m,
  goto_functionst &goto_functions)
{
  remove_returnst rr(symbol_table, m);
  rr(goto_functions);
}

void remove_returns(
  goto_model_functiont &goto_model_function,
  message_handlert &m,
  function_is_stubt function_is_stub)
{
  remove_returnst rr(goto_model_function.get_symbol_table(), m);
  rr(goto_model_function, function_is_stub);
}

/// removes returns
void remove_returns(goto_modelt &goto_model, message_handlert &m)
{
  remove_returnst rr(goto_model.symbol_table, m);
  rr.build_fp_targets(goto_model);
  rr(goto_model.goto_functions);
}

/// turns an assignment to fkt#return_value back into 'return x'
bool remove_returnst::restore_returns(
  goto_functionst::function_mapt::iterator f_it)
{
  const irep_idt function_id=f_it->first;

  // do we have X#return_value?
  auto rv_name = return_value_identifier(function_id);
  symbol_tablet::symbolst::const_iterator rv_it=
    symbol_table.symbols.find(rv_name);
  if(rv_it==symbol_table.symbols.end())
    return true;

  // remove the return_value symbol from the symbol_table
  irep_idt rv_name_id=rv_it->second.name;
  symbol_table.erase(rv_it);

  goto_programt &goto_program=f_it->second.body;

  bool did_something = false;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_assign())
    {
      const auto &assign = i_it->get_assign();

      if(assign.lhs().id()!=ID_symbol ||
         to_symbol_expr(assign.lhs()).get_identifier()!=rv_name_id)
        continue;

      // replace "fkt#return_value=x;" by "return x;"
      const exprt rhs = assign.rhs();
      *i_it =
        goto_programt::make_return(code_returnt(rhs), i_it->source_location);
      did_something = true;
    }
  }

  if(did_something)
    remove_skip(goto_program);

  return false;
}

/// turns f(...); lhs=f#return_value; into lhs=f(...)
void remove_returnst::undo_function_calls(
  goto_programt &goto_program)
{
  namespacet ns(symbol_table);

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_function_call())
    {
      code_function_callt function_call = i_it->get_function_call();

      // ignore function pointers
      if(function_call.function().id()!=ID_symbol)
        continue;

      const irep_idt function_id=
        to_symbol_expr(function_call.function()).get_identifier();

      // find "f(...); lhs=f#return_value; DEAD f#return_value;"
      // and revert to "lhs=f(...);"
      goto_programt::instructionst::iterator next = std::next(i_it);

      INVARIANT(
        next!=goto_program.instructions.end(),
        "non-void function call must be followed by #return_value read");

      if(!next->is_assign())
        continue;

      const code_assignt &assign = next->get_assign();

      const auto rv_symbol = return_value_symbol(function_id, ns);
      if(assign.rhs() != rv_symbol)
        continue;

      // restore the previous assignment
      function_call.lhs()=assign.lhs();

      i_it->set_function_call(function_call);

      // remove the assignment and subsequent dead
      // i_it remains valid
      next=goto_program.instructions.erase(next);
      INVARIANT(
        next!=goto_program.instructions.end() && next->is_dead(),
        "read from #return_value should be followed by DEAD #return_value");
      // i_it remains valid
      goto_program.instructions.erase(next);
    }
  }
}

void remove_returnst::restore(goto_functionst &goto_functions)
{
  // restore all types first
  bool unmodified=true;
  Forall_goto_functions(it, goto_functions)
    unmodified=restore_returns(it) && unmodified;

  if(!unmodified)
  {
    Forall_goto_functions(it, goto_functions)
      undo_function_calls(it->second.body);
  }
}

/// restores return statements
void restore_returns(goto_modelt &goto_model, message_handlert &m)
{
  remove_returnst rr(goto_model.symbol_table, m);
  rr.restore(goto_model.goto_functions);
}

irep_idt return_value_identifier(const irep_idt &identifier)
{
  return id2string(identifier) + RETURN_VALUE_SUFFIX;
}

symbol_exprt
return_value_symbol(const irep_idt &identifier, const namespacet &ns)
{
  const symbolt &function_symbol = ns.lookup(identifier);
  const typet &return_type = to_code_type(function_symbol.type).return_type();
  return symbol_exprt(return_value_identifier(identifier), return_type);
}

bool is_return_value_identifier(const irep_idt &id)
{
  return has_suffix(id2string(id), RETURN_VALUE_SUFFIX);
}

bool is_return_value_symbol(const symbol_exprt &symbol_expr)
{
  return is_return_value_identifier(symbol_expr.get_identifier());
}

void remove_returnst::do_function_call_complete(
  goto_programt::targett target,
  goto_programt &goto_program)
{
  const auto &function_call = target->get_function_call();
  const auto &function_id =
    to_symbol_expr(function_call.function()).get_identifier();

  // The return type in the definition of the function may differ
  // from the return type in the declaration.  We therefore do a
  // cast.
  optionalt<symbol_exprt> return_value =
    get_or_create_return_value_symbol(function_id);
  CHECK_RETURN(return_value.has_value());

  // replace "lhs=f(...)" by
  // "f(...); lhs=f#return_value; DEAD f#return_value;"
  goto_programt::targett t_a = goto_program.insert_after(
    target,
    goto_programt::make_assignment(
      code_assignt{function_call.lhs(),
                   typecast_exprt::conditional_cast(
                     *return_value, function_call.lhs().type())},
      target->source_location));

  goto_program.insert_after(
    t_a, goto_programt::make_dead(*return_value, target->source_location));
}

void remove_returnst::do_function_call_complete(
  goto_programt::targett target,
  const possible_fp_targetst &possible_fp_targets,
  goto_programt &goto_program)
{
  PRECONDITION(target->is_function_call());
  const auto &function_call = target->get_function_call();
  PRECONDITION(function_call.function().id() == ID_dereference);
  const auto &function_symbol =
    to_dereference_expr(function_call.function()).pointer();
  PRECONDITION(function_symbol.id() == ID_symbol);
  const auto &function_id = to_symbol_expr(function_symbol).get_identifier();
  if(possible_fp_targets.empty())
    throw incorrect_goto_program_exceptiont{
      "the function pointer " + id2string(function_id) +
        " does not have any potential targets",
      target->source_location};

  cond_exprt rhs(exprt::operandst{}, function_call.lhs().type());
  std::vector<symbol_exprt> return_values;

  const auto &first_target_id = possible_fp_targets.begin()->get_identifier();
  const auto first_target_symbol = symbol_table.lookup(first_target_id);
  CHECK_RETURN(first_target_symbol);

  auto &pointer_lhs_symbol = get_fresh_aux_symbol(
    pointer_type(function_call.lhs().type()),
    "", // no name prefix
    "p_lhs",
    target->source_location,
    first_target_symbol->mode,
    symbol_table);
  symbol_exprt pointer_lhs_expr = pointer_lhs_symbol.symbol_expr();

  exprt::operandst disjunction_operands;

  for(const auto &target_expr : possible_fp_targets)
  {
    irep_idt target_id = target_expr.get_identifier();
    const symbolt *target_symbol = symbol_table.lookup(target_id);
    CHECK_RETURN(target_symbol);

    // The return type in the definition of the function may differ
    // from the return type in the declaration.  We therefore do a
    // cast.
    optionalt<symbol_exprt> return_value =
      get_or_create_return_value_symbol(target_id);
    CHECK_RETURN(return_value.has_value());
    return_values.push_back(*return_value);

    const auto f_equals_f_i = equal_exprt{
      function_call.function(), address_of_exprt{target_symbol->symbol_expr()}};
    disjunction_operands.push_back(f_equals_f_i);
    rhs.add_case(f_equals_f_i, address_of_exprt{*return_value});
  }

  // replace "lhs=*f(...)" by
  //
  // assert(f==f1 || f==f2 || ..); // so that the user knows
  // assume(f==f1 || f==f2 || ..); // so that we abort this execution
  // T* p_lhs = lhs = (f == f1 ? &f1#return_value : f == f2
  //                           ? &f2#return_value .. );
  // f*(...);
  // lhs = *p_lhs;
  // DEAD f1#return_value;
  // DEAD f2#return_value;
  // ..
  // DEAD p_lhs
  goto_program.insert_before(
    target,
    goto_programt::make_assertion(
      disjunction(disjunction_operands), target->source_location));
  goto_program.insert_before(
    target,
    goto_programt::make_assumption(
      disjunction(disjunction_operands), target->source_location));
  goto_program.insert_before(
    target,
    goto_programt::make_assignment(
      code_assignt{pointer_lhs_expr, rhs}, target->source_location));
  goto_programt::targett t_a = goto_program.insert_after(
    target,
    goto_programt::make_assignment(
      code_assignt{function_call.lhs(), dereference_exprt{pointer_lhs_expr}},
      target->source_location));

  for(const auto &return_value : return_values)
    t_a = goto_program.insert_after(
      t_a, goto_programt::make_dead(return_value, target->source_location));
  goto_program.insert_after(
    t_a, goto_programt::make_dead(pointer_lhs_expr, target->source_location));
}

void remove_returnst::do_function_call_stub(
  goto_programt::targett target,
  goto_programt &goto_program)
{
  const auto &function_call = target->get_function_call();

  // replace "lhs=f(...)" by "f(...); lhs=nondet;"
  goto_program.insert_after(
    target,
    goto_programt::make_assignment(
      code_assignt{function_call.lhs(),
                   side_effect_expr_nondett{function_call.lhs().type(),
                                            target->source_location}},
      target->source_location));
}

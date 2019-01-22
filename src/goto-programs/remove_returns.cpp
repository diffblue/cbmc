/*******************************************************************\

Module: Remove function return values

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

/// \file
/// Remove function return values

#include "remove_returns.h"

#include <util/std_expr.h>

#include "goto_model.h"

#include "remove_skip.h"

class remove_returnst
{
public:
  explicit remove_returnst(symbol_table_baset &_symbol_table):
    symbol_table(_symbol_table)
  {
  }

  void operator()(
    goto_functionst &goto_functions);

  void operator()(
    goto_model_functiont &model_function,
    function_is_stubt function_is_stub);

  void restore(
    goto_functionst &goto_functions);

protected:
  symbol_table_baset &symbol_table;

  void replace_returns(
    const irep_idt &function_id,
    goto_functionst::goto_functiont &function);

  void do_function_calls(
    function_is_stubt function_is_stub,
    goto_programt &goto_program);

  bool restore_returns(
    goto_functionst::function_mapt::iterator f_it);

  void undo_function_calls(
    goto_programt &goto_program);

  optionalt<symbol_exprt>
  get_or_create_return_value_symbol(const irep_idt &function_id);
};

optionalt<symbol_exprt>
remove_returnst::get_or_create_return_value_symbol(const irep_idt &function_id)
{
  const irep_idt symbol_name = id2string(function_id) + RETURN_VALUE_SUFFIX;
  const symbolt *existing_symbol = symbol_table.lookup(symbol_name);
  if(existing_symbol != nullptr)
    return existing_symbol->symbol_expr();

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

  // look up the function symbol
  symbolt &function_symbol = *symbol_table.get_writeable(function_id);

  // make the return type 'void'
  function.type.return_type() = empty_typet();
  function_symbol.type = function.type;

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
        i_it->make_assignment(assignment);
      }
      else
        i_it->make_skip();
    }
  }
}

/// turns x=f(...) into f(...); lhs=f#return_value;
/// \param function_is_stub: function (irep_idt -> bool) that determines whether
///   a given function ID is a stub
/// \param goto_program: program to transform
void remove_returnst::do_function_calls(
  function_is_stubt function_is_stub,
  goto_programt &goto_program)
{
  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_function_call())
    {
      code_function_callt &function_call = i_it->get_function_call();

      INVARIANT(
        function_call.function().id() == ID_symbol,
        "indirect function calls should have been removed prior to running "
        "remove-returns");

      const irep_idt function_id =
        to_symbol_expr(function_call.function()).get_identifier();

      optionalt<symbol_exprt> return_value;
      typet old_return_type;
      bool is_stub = function_is_stub(function_id);

      if(is_stub)
      {
        old_return_type =
          to_code_type(function_call.function().type()).return_type();
      }
      else
      {
        // The callee may or may not already have been transformed by this pass,
        // so its symbol-table entry may already have void return type.
        // To simplify matters, create its return-value global now (if not
        // already done), and use that to determine its true return type.
        return_value = get_or_create_return_value_symbol(function_id);
        if(!return_value.has_value()) // really void-typed?
          continue;
        old_return_type = return_value->type();
      }

      // Do we return anything?
      if(old_return_type != empty_typet())
      {
        // replace "lhs=f(...)" by
        // "f(...); lhs=f#return_value; DEAD f#return_value;"

        // fix the type
        to_code_type(function_call.function().type()).return_type()=
          empty_typet();

        if(function_call.lhs().is_not_nil())
        {
          exprt rhs;

          if(!is_stub)
          {
            // The return type in the definition of the function may differ
            // from the return type in the declaration.  We therefore do a
            // cast.
            rhs = typecast_exprt::conditional_cast(
              *return_value, function_call.lhs().type());
          }
          else
            rhs = side_effect_expr_nondett(
              function_call.lhs().type(), i_it->source_location);

          goto_programt::targett t_a=goto_program.insert_after(i_it);
          t_a->make_assignment();
          t_a->source_location=i_it->source_location;
          t_a->code=code_assignt(function_call.lhs(), rhs);
          t_a->function=i_it->function;

          // fry the previous assignment
          function_call.lhs().make_nil();

          if(!is_stub)
          {
            goto_programt::targett t_d=goto_program.insert_after(t_a);
            t_d->make_dead();
            t_d->source_location=i_it->source_location;
            t_d->code = code_deadt(*return_value);
            t_d->function=i_it->function;
          }
        }
      }
    }
  }
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
    do_function_calls(function_is_stub, it->second.body);
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
  do_function_calls(function_is_stub, goto_function.body);
}

/// removes returns
void remove_returns(
  symbol_table_baset &symbol_table,
  goto_functionst &goto_functions)
{
  remove_returnst rr(symbol_table);
  rr(goto_functions);
}

/// Removes returns from a single function. Only usable with Java programs at
/// the moment; to use it with other languages, they must annotate their stub
/// functions with ID_C_incomplete as currently done in
/// java_bytecode_convert_method.cpp.
///
/// This will generate \#return_value variables, if not already present, for
/// both the function being altered *and* any callees.
/// \param goto_model_function: function to transform
/// \param function_is_stub: function that will be used to test whether a given
///   callee has been or will be given a body. It should return true if so, or
///   false if the function will remain a bodyless stub.
void remove_returns(
  goto_model_functiont &goto_model_function,
  function_is_stubt function_is_stub)
{
  remove_returnst rr(goto_model_function.get_symbol_table());
  rr(goto_model_function, function_is_stub);
}

/// removes returns
void remove_returns(goto_modelt &goto_model)
{
  remove_returnst rr(goto_model.symbol_table);
  rr(goto_model.goto_functions);
}

/// Get code type of a function that has had remove_returns run upon it
/// \param symbol_table: global symbol table
/// \param function_id: function to get the type of
/// \return the function's type with its `return_type()` restored to its
///   original value
code_typet original_return_type(
  const symbol_table_baset &symbol_table,
  const irep_idt &function_id)
{
  // look up the function symbol
  const symbolt &function_symbol = symbol_table.lookup_ref(function_id);
  code_typet type = to_code_type(function_symbol.type);

  // do we have X#return_value?
  std::string rv_name=id2string(function_id)+RETURN_VALUE_SUFFIX;

  symbol_tablet::symbolst::const_iterator rv_it=
    symbol_table.symbols.find(rv_name);

  if(rv_it != symbol_table.symbols.end())
    type.return_type() = rv_it->second.type;

  return type;
}

/// turns an assignment to fkt#return_value back into 'return x'
bool remove_returnst::restore_returns(
  goto_functionst::function_mapt::iterator f_it)
{
  const irep_idt function_id=f_it->first;

  // do we have X#return_value?
  std::string rv_name=id2string(function_id)+RETURN_VALUE_SUFFIX;

  symbol_tablet::symbolst::const_iterator rv_it=
    symbol_table.symbols.find(rv_name);

  if(rv_it==symbol_table.symbols.end())
    return true;

  // look up the function symbol
  symbolt &function_symbol=*symbol_table.get_writeable(function_id);

  // restore the return type
  f_it->second.type=original_return_type(symbol_table, function_id);
  function_symbol.type=f_it->second.type;

  // remove the return_value symbol from the symbol_table
  irep_idt rv_name_id=rv_it->second.name;
  symbol_table.erase(rv_it);

  goto_programt &goto_program=f_it->second.body;

  bool did_something = false;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_assign())
    {
      code_assignt &assign = i_it->get_assign();
      if(assign.lhs().id()!=ID_symbol ||
         to_symbol_expr(assign.lhs()).get_identifier()!=rv_name_id)
        continue;

      // replace "fkt#return_value=x;" by "return x;"
      const exprt rhs = assign.rhs();
      i_it->make_return();
      i_it->code = code_returnt(rhs);
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
      code_function_callt &function_call = i_it->get_function_call();

      // ignore function pointers
      if(function_call.function().id()!=ID_symbol)
        continue;

      const irep_idt function_id=
        to_symbol_expr(function_call.function()).get_identifier();

      const symbolt &function_symbol=ns.lookup(function_id);

      // fix the type
      to_code_type(function_call.function().type()).return_type()=
        to_code_type(function_symbol.type).return_type();

      // find "f(...); lhs=f#return_value; DEAD f#return_value;"
      // and revert to "lhs=f(...);"
      goto_programt::instructionst::iterator next=i_it;
      ++next;
      INVARIANT(
        next!=goto_program.instructions.end(),
        "non-void function call must be followed by #return_value read");

      if(!next->is_assign())
        continue;

      const code_assignt &assign = next->get_assign();

      if(assign.rhs().id()!=ID_symbol)
        continue;

      irep_idt rv_name=id2string(function_id)+RETURN_VALUE_SUFFIX;
      const symbol_exprt &rhs=to_symbol_expr(assign.rhs());
      if(rhs.get_identifier()!=rv_name)
        continue;

      // restore the previous assignment
      function_call.lhs()=assign.lhs();

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
void restore_returns(goto_modelt &goto_model)
{
  remove_returnst rr(goto_model.symbol_table);
  rr.restore(goto_model.goto_functions);
}

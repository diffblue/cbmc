/*******************************************************************\

Module: Remove function return values

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

/// \file
/// Replace function returns by assignments to global variables

#include "remove_returns.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/suffix.h>

#include "goto_model.h"

#include "remove_skip.h"

#define RETURN_VALUE_SUFFIX "#return_value"

class remove_returnst
{
public:
  explicit remove_returnst(symbol_table_baset &_symbol_table):
    symbol_table(_symbol_table)
  {
  }

  void operator()(
    goto_functionst &goto_functions);

  void operator()(goto_model_functiont &model_function);

  void restore(
    goto_functionst &goto_functions);

protected:
  symbol_table_baset &symbol_table;

  void replace_returns(
    const irep_idt &function_id,
    goto_functionst::goto_functiont &function);

  bool do_function_calls(goto_programt &goto_program, irep_idt mode);

  bool restore_returns(
    goto_functionst::function_mapt::iterator f_it,
    std::set<irep_idt> &rv_identifiers);

  void undo_function_calls(
    goto_programt &goto_program);

  optionalt<symbol_exprt>
  get_or_create_return_value_symbol(const typet &return_type, irep_idt mode);
};

irep_idt return_value_identifier(const typet &type)
{
  if(type.id() == ID_pointer)
  {
    // we don't care about the subtype -- we simply rely on a cast
    return type.id_string() +
           std::to_string(to_pointer_type(type).get_width()) +
           RETURN_VALUE_SUFFIX;
  }
  else if(type.id() == ID_bool)
  {
    return type.id_string() + RETURN_VALUE_SUFFIX;
  }
  else if(type.id() == ID_vector)
  {
    return type.id_string() +
           integer2string(
             numeric_cast_v<mp_integer>(to_vector_type(type).size())) +
           "-" +
           id2string(return_value_identifier(to_vector_type(type).subtype()));
  }
  else if(type.id() == ID_complex)
  {
    return type.id_string() + '-' +
           id2string(return_value_identifier(to_complex_type(type).subtype()));
  }
  else if(
    type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
    type.id() == ID_c_bool ||
    type.id() == ID_floatbv || type.id() == ID_fixedbv)
  {
    return type.id_string() +
           std::to_string(to_bitvector_type(type).get_width()) +
           RETURN_VALUE_SUFFIX;
  }
  else if(
    type.id() == ID_c_enum_tag || type.id() == ID_struct_tag ||
    type.id() == ID_union_tag)
  {
    return type.id_string() + '-' +
           id2string(to_tag_type(type).get_identifier()) + RETURN_VALUE_SUFFIX;
  }
  else
    return std::string("unknown") + RETURN_VALUE_SUFFIX;
}

irep_idt
return_value_identifier(const irep_idt &identifier, const namespacet &ns)
{
  const symbolt &function_symbol = ns.lookup(identifier);
  const typet &return_type = to_code_type(function_symbol.type).return_type();
  return return_value_identifier(return_type);
}

typet return_value_type(typet src)
{
  if(src.id() == ID_pointer)
  {
    // turn anything into 'void *'
    pointer_typet result(to_pointer_type(src));
    result.subtype() = empty_typet();
    return std::move(result);
  }
  else
    return src;
}

optionalt<symbol_exprt> remove_returnst::get_or_create_return_value_symbol(
  const typet &return_type,
  irep_idt mode)
{
  if(return_type == empty_typet())
    return {};

  const irep_idt symbol_name = return_value_identifier(return_type);
  const symbolt *existing_symbol = symbol_table.lookup(symbol_name);
  if(existing_symbol != nullptr)
    return existing_symbol->symbol_expr();

  auxiliary_symbolt new_symbol;
  new_symbol.is_static_lifetime = true;
  new_symbol.base_name = symbol_name;
  new_symbol.mode = mode;
  new_symbol.name = symbol_name;
  new_symbol.type = return_value_type(return_type);
  // Return-value symbols will always be written before they are read, so there
  // is no need for __CPROVER_initialize to do anything:
  new_symbol.type.set(ID_C_no_initialization_required, true);

  symbol_table.add(new_symbol);
  return new_symbol.symbol_expr();
}

/// turns 'return x' into an assignment to return_type#return_value
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

  const namespacet ns(symbol_table);
  const auto &function_symbol = ns.lookup(function_id);

  // add return_value symbol to symbol_table, if not already created:
  const auto return_symbol =
    get_or_create_return_value_symbol(return_type, function_symbol.mode);

  for(auto &i : function.body.instructions)
  {
    if(i.is_return())
    {
      INVARIANT(
        i.code.operands().size() == 1,
        "return instructions should have one operand");

      if(return_symbol.has_value())
      {
        // The return type may differ from the type of the symbol.
        // We therefore do a cast.
        auto rhs = typecast_exprt::conditional_cast(
          i.get_return().return_value(), return_symbol->type());

        // replace "return x;" by "return_type#return_value=x;"
        code_assignt assignment(*return_symbol, rhs);

        // Now turn the `return' into `assignment'.
        i = goto_programt::make_assignment(assignment, i.source_location);
      }
      else
        i.turn_into_skip();
    }
  }
}

/// turns x=f(...) into f(...); lhs=return_type#return_value;
/// \param goto_program: program to transform
/// \return True if, and only if, instructions have been inserted. In that case
///   the caller must invoke an appropriate method to update location numbers.
bool remove_returnst::do_function_calls(
  goto_programt &goto_program,
  irep_idt mode)
{
  bool requires_update = false;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_function_call())
    {
      code_function_callt function_call = i_it->get_function_call();

      const auto &return_type =
        to_code_type(function_call.function().type()).return_type();

      // Do we return anything?
      if(does_function_call_return(function_call))
      {
        // replace "lhs=f(...)" by
        // "f(...); lhs=return_type#return_value; DEAD return_type#return_value;"

        exprt rhs;

        optionalt<symbol_exprt> return_value;

        return_value = get_or_create_return_value_symbol(return_type, mode);
        CHECK_RETURN(return_value.has_value());

        // havoc the #return_value variable

        exprt nondet =
          side_effect_expr_nondett(return_value->type(), i_it->source_location);

        goto_program.insert_before_swap(i_it);
        *i_it = goto_programt::make_assignment(
          code_assignt(*return_value, nondet), i_it->source_location);

        goto_programt::targett call_it = std::next(i_it);

        // The return type may differ from the type of the symbol.
        // We therefore do a cast.
        rhs = typecast_exprt::conditional_cast(
          *return_value, function_call.lhs().type());

        goto_programt::targett t_a = goto_program.insert_after(
          call_it,
          goto_programt::make_assignment(
            code_assignt(function_call.lhs(), rhs), call_it->source_location));

        // fry the previous assignment
        function_call.lhs().make_nil();

        goto_program.insert_after(
          t_a,
          goto_programt::make_dead(*return_value, call_it->source_location));

        // update the call
        call_it->set_function_call(function_call);

        requires_update = true;
      }
    }
  }

  return requires_update;
}

void remove_returnst::operator()(goto_functionst &goto_functions)
{
  const namespacet ns(symbol_table);

  for(auto &f : goto_functions.function_map)
  {
    auto mode = ns.lookup(f.first).mode;

    replace_returns(f.first, f.second);
    if(do_function_calls(f.second.body, mode))
      goto_functions.compute_location_numbers(f.second.body);
  }
}

void remove_returnst::operator()(goto_model_functiont &model_function)
{
  goto_functionst::goto_functiont &goto_function =
    model_function.get_goto_function();

  // If this is a stub it doesn't have a corresponding #return_value,
  // not any return instructions to alter:
  if(goto_function.body.empty())
    return;

  irep_idt function_id = model_function.get_function_id();

  replace_returns(function_id, goto_function);

  const namespacet ns(symbol_table);
  irep_idt mode = ns.lookup(function_id).mode;

  if(do_function_calls(goto_function.body, mode))
    model_function.compute_location_numbers();
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
void remove_returns(goto_model_functiont &goto_model_function)
{
  remove_returnst rr(goto_model_function.get_symbol_table());
  rr(goto_model_function);
}

/// removes returns
void remove_returns(goto_modelt &goto_model)
{
  remove_returnst rr(goto_model.symbol_table);
  rr(goto_model.goto_functions);
}

/// turns an assignment to return_type#return_value back into 'return x'
bool remove_returnst::restore_returns(
  goto_functionst::function_mapt::iterator f_it,
  std::set<irep_idt> &rv_identifiers)
{
  // do we have return_type#return_value?
  auto rv_symbol = return_value_symbol(f_it->second.type);
  auto rv_id = rv_symbol.get_identifier();

  symbol_tablet::symbolst::const_iterator rv_it =
    symbol_table.symbols.find(rv_id);

  if(rv_it==symbol_table.symbols.end())
    return true;

  rv_identifiers.insert(rv_id);

  goto_programt &goto_program=f_it->second.body;

  bool did_something = false;

  for(auto &i : goto_program.instructions)
  {
    if(i.is_assign())
    {
      const auto &assign = i.get_assign();

      if(
        assign.lhs().id() != ID_symbol ||
        to_symbol_expr(assign.lhs()).get_identifier() != rv_id)
        continue;

      // replace "return_type#return_value=x;" by "return x;"
      const exprt rhs = assign.rhs();
      i = goto_programt::make_return(code_returnt(rhs), i.source_location);
      did_something = true;
    }
  }

  if(did_something)
    remove_skip(goto_program);

  return false;
}

/// turns f(...); lhs=return_type#return_value; into lhs=f(...)
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

      // find "f(...); lhs=return_type#return_value; DEAD return_type#return_value;"
      // and revert to "lhs=f(...);"
      goto_programt::instructionst::iterator next = std::next(i_it);

      INVARIANT(
        next!=goto_program.instructions.end(),
        "non-void function call must be followed by #return_value read");

      if(!next->is_assign())
        continue;

      const code_assignt &assign = next->get_assign();

      const auto rv_symbol =
        return_value_symbol(to_code_type(function_call.function().type()));
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
  std::set<irep_idt> rv_identifiers;

  bool unmodified=true;
  Forall_goto_functions(it, goto_functions)
    unmodified=restore_returns(it, rv_identifiers) && unmodified;

  if(!unmodified)
  {
    Forall_goto_functions(it, goto_functions)
      undo_function_calls(it->second.body);
  }

  // remove the return_value symbols from the symbol_table
  for(auto id : rv_identifiers)
    symbol_table.remove(id);
}

/// restores return statements
void restore_returns(goto_modelt &goto_model)
{
  remove_returnst rr(goto_model.symbol_table);
  rr.restore(goto_model.goto_functions);
}

symbol_exprt
return_value_symbol(const irep_idt &identifier, const namespacet &ns)
{
  const symbolt &function_symbol = ns.lookup(identifier);
  const typet &return_type = to_code_type(function_symbol.type).return_type();
  return symbol_exprt(return_value_identifier(return_type), return_type);
}

symbol_exprt return_value_symbol(const code_typet &code_type)
{
  const typet &return_type = code_type.return_type();
  return symbol_exprt(
    return_value_identifier(return_type), return_value_type(return_type));
}

bool is_return_value_identifier(const irep_idt &id)
{
  return has_suffix(id2string(id), RETURN_VALUE_SUFFIX);
}

bool is_return_value_symbol(const symbol_exprt &symbol_expr)
{
  return is_return_value_identifier(symbol_expr.get_identifier());
}

bool does_function_call_return(const code_function_callt &function_call)
{
  return to_code_type(function_call.function().type()).return_type() !=
           empty_typet() &&
         function_call.lhs().is_not_nil();
}

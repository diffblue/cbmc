/*******************************************************************\

Module: State Encoding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "state_encoding.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>

#include <goto-programs/goto_model.h>

#include "equality_propagation.h"
#include "instrument_contracts.h"
#include "sentinel_dll.h"
#include "solver.h"
#include "state.h"
#include "state_encoding_targets.h"
#include "variable_encoding.h"

#include <iostream>

class state_encodingt
{
public:
  explicit state_encodingt(const goto_modelt &__goto_model)
    : goto_model(__goto_model)
  {
  }

  void operator()(
    const goto_functionst::function_mapt::const_iterator,
    encoding_targett &);

  void encode(
    const goto_functiont &,
    const irep_idt function_identifier,
    const std::string &state_prefix,
    const std::vector<irep_idt> &call_stack,
    const std::string &annotation,
    const symbol_exprt &entry_state,
    const exprt &return_lhs,
    encoding_targett &);

protected:
  using loct = goto_programt::const_targett;
  const goto_modelt &goto_model;

  symbol_exprt out_state_expr(loct) const;
  symbol_exprt state_expr_with_suffix(loct, const std::string &suffix) const;
  symbol_exprt out_state_expr(loct, bool taken) const;
  symbol_exprt in_state_expr(loct) const;
  std::vector<symbol_exprt> incoming_symbols(loct) const;
  exprt evaluate_expr(loct, const exprt &, const exprt &) const;
  exprt evaluate_expr_rec(
    loct,
    const exprt &,
    const exprt &,
    const std::unordered_set<symbol_exprt, irep_hash> &) const;
  exprt replace_nondet_rec(
    loct,
    const exprt &,
    std::vector<symbol_exprt> &nondet_symbols) const;
  exprt evaluate_expr(loct, const exprt &) const;
  exprt address_rec(loct, const exprt &, exprt) const;
  static exprt state_lambda_expr(exprt);
  exprt forall_states_expr(loct, exprt) const;
  exprt forall_states_expr(loct, exprt, exprt) const;
  void setup_incoming(const goto_functiont &);
  exprt assignment_constraint(loct, exprt lhs, exprt rhs) const;
  exprt assignment_constraint_rec(
    loct,
    exprt state,
    exprt lhs,
    exprt rhs,
    std::vector<symbol_exprt> &nondet_symbols) const;
  void function_call(goto_programt::const_targett, encoding_targett &);
  void function_call_symbol(goto_programt::const_targett, encoding_targett &);

  irep_idt function_identifier;
  std::string state_prefix;
  std::string annotation;
  std::vector<irep_idt> call_stack;
  loct first_loc;
  symbol_exprt entry_state = symbol_exprt(irep_idt(), typet());
  exprt return_lhs = nil_exprt();
  using incomingt = std::map<loct, std::vector<loct>>;
  incomingt incoming;

  static symbol_exprt va_args(irep_idt function);
};

symbol_exprt state_encodingt::out_state_expr(loct loc) const
{
  return state_expr_with_suffix(loc, "");
}

symbol_exprt state_encodingt::state_expr_with_suffix(
  loct loc,
  const std::string &suffix) const
{
  irep_idt identifier =
    state_prefix + std::to_string(loc->location_number) + suffix;
  return symbol_exprt(identifier, state_predicate_type());
}

symbol_exprt state_encodingt::out_state_expr(loct loc, bool taken) const
{
  return state_expr_with_suffix(loc, taken ? "T" : "");
}

std::vector<symbol_exprt> state_encodingt::incoming_symbols(loct loc) const
{
  auto incoming_it = incoming.find(loc);

  DATA_INVARIANT(incoming_it != incoming.end(), "incoming is complete");

  std::vector<symbol_exprt> symbols;
  symbols.reserve(incoming_it->second.size());

  for(auto &loc_in : incoming_it->second)
  {
    std::string suffix;

    // conditional jump from loc_in to loc?
    if(
      loc_in->is_goto() && !loc_in->condition().is_true() &&
      loc != std::next(loc_in))
    {
      suffix = "T";
    }

    symbols.push_back(state_expr_with_suffix(loc_in, suffix));
  }

  return symbols;
}

symbol_exprt state_encodingt::in_state_expr(loct loc) const
{
  if(loc == first_loc)
    return entry_state;

  auto incoming_symbols = this->incoming_symbols(loc);

  if(incoming_symbols.size() == 1)
    return incoming_symbols.front();
  else
    return state_expr_with_suffix(loc, "in");
}

exprt state_encodingt::evaluate_expr(
  loct loc,
  const exprt &state,
  const exprt &what) const
{
  return evaluate_expr_rec(loc, state, what, {});
}

exprt state_encodingt::replace_nondet_rec(
  loct loc,
  const exprt &what,
  std::vector<symbol_exprt> &nondet_symbols) const
{
  if(what.id() == ID_side_effect)
  {
    auto &side_effect = to_side_effect_expr(what);
    auto statement = side_effect.get_statement();
    if(statement == ID_nondet)
    {
      irep_idt identifier = "nondet::" + state_prefix +
                            std::to_string(loc->location_number) + "-" +
                            std::to_string(nondet_symbols.size());
      auto symbol = symbol_exprt(identifier, side_effect.type());
      nondet_symbols.push_back(symbol);
      return std::move(symbol);
    }
    else if(statement == ID_va_start)
    {
      // return address of va_args array
      return typecast_exprt::conditional_cast(
        evaluate_expr(loc, state_expr(), va_args(function_identifier)),
        what.type());
    }
    else
      return what; // leave it
  }
  else
  {
    exprt tmp = what;
    for(auto &op : tmp.operands())
      op = replace_nondet_rec(loc, op, nondet_symbols);
    return tmp;
  }
}

exprt state_encodingt::evaluate_expr_rec(
  loct loc,
  const exprt &state,
  const exprt &what,
  const std::unordered_set<symbol_exprt, irep_hash> &bound_symbols) const
{
  PRECONDITION(state.type().id() == ID_state);

  if(what.id() == ID_symbol)
  {
    const auto &symbol_expr = to_symbol_expr(what);

    if(symbol_expr.get_identifier() == CPROVER_PREFIX "return_value")
    {
      auto new_symbol = symbol_exprt("return_value", what.type());
      return evaluate_exprt(
        state, address_rec(loc, state, new_symbol), what.type());
    }
    else if(bound_symbols.find(symbol_expr) == bound_symbols.end())
    {
      return evaluate_exprt(state, address_rec(loc, state, what), what.type());
    }
    else
      return what; // leave as is
  }
  else if(
    what.id() == ID_dereference || what.id() == ID_member ||
    what.id() == ID_index)
  {
    return evaluate_exprt(state, address_rec(loc, state, what), what.type());
  }
  else if(what.id() == ID_forall || what.id() == ID_exists)
  {
    auto new_quantifier_expr = to_quantifier_expr(what); // copy
    auto new_bound_symbols = bound_symbols;              // copy

    for(const auto &v : new_quantifier_expr.variables())
      new_bound_symbols.insert(v);

    new_quantifier_expr.where() = evaluate_expr_rec(
      loc, state, new_quantifier_expr.where(), new_bound_symbols);

    return std::move(new_quantifier_expr);
  }
  else if(what.id() == ID_address_of)
  {
    const auto &object = to_address_of_expr(what).object();
    return address_rec(loc, state, object);
  }
  else if(what.id() == ID_live_object)
  {
    const auto &live_object_expr = to_live_object_expr(what);
    auto pointer =
      evaluate_expr_rec(loc, state, live_object_expr.pointer(), bound_symbols);
    return state_live_object_exprt(state, pointer);
  }
  else if(what.id() == ID_writeable_object)
  {
    const auto &writeable_object_expr = to_writeable_object_expr(what);
    auto pointer = evaluate_expr_rec(
      loc, state, writeable_object_expr.pointer(), bound_symbols);
    return state_writeable_object_exprt(state, pointer);
  }
  else if(what.id() == ID_is_dynamic_object)
  {
    const auto &is_dynamic_object_expr = to_is_dynamic_object_expr(what);
    auto pointer = evaluate_expr_rec(
      loc, state, is_dynamic_object_expr.address(), bound_symbols);
    return state_is_dynamic_object_exprt(state, pointer);
  }
  else if(what.id() == ID_object_size)
  {
    const auto &object_size_expr = to_object_size_expr(what);
    auto pointer =
      evaluate_expr_rec(loc, state, object_size_expr.pointer(), bound_symbols);
    return state_object_size_exprt(state, pointer, what.type());
  }
  else if(what.id() == ID_r_ok || what.id() == ID_w_ok || what.id() == ID_rw_ok)
  {
    // we need to add the state
    const auto &r_or_w_ok_expr = to_r_or_w_ok_expr(what);
    auto pointer =
      evaluate_expr_rec(loc, state, r_or_w_ok_expr.pointer(), bound_symbols);
    auto size =
      evaluate_expr_rec(loc, state, r_or_w_ok_expr.size(), bound_symbols);
    auto new_id = what.id() == ID_r_ok   ? ID_state_r_ok
                  : what.id() == ID_w_ok ? ID_state_w_ok
                                         : ID_state_rw_ok;
    return ternary_exprt(new_id, state, pointer, size, what.type());
  }
  else if(what.id() == ID_is_cstring)
  {
    // we need to add the state
    const auto &is_cstring_expr = to_unary_expr(what);
    auto pointer =
      evaluate_expr_rec(loc, state, is_cstring_expr.op(), bound_symbols);
    return binary_predicate_exprt(state, ID_state_is_cstring, pointer);
  }
  else if(what.id() == ID_cstrlen)
  {
    // we need to add the state
    const auto &cstrlen_expr = to_cstrlen_expr(what);
    auto address =
      evaluate_expr_rec(loc, state, cstrlen_expr.op(), bound_symbols);
    return state_cstrlen_exprt(state, address, cstrlen_expr.type());
  }
  else if(what.id() == ID_is_sentinel_dll)
  {
    // we need to add the state
    if(what.operands().size() == 2)
    {
      const auto &is_sentinel_dll_expr = to_binary_expr(what);
      auto head = evaluate_expr_rec(
        loc, state, is_sentinel_dll_expr.op0(), bound_symbols);
      auto tail = evaluate_expr_rec(
        loc, state, is_sentinel_dll_expr.op1(), bound_symbols);
      return state_is_sentinel_dll_exprt(state, head, tail);
    }
    else if(what.operands().size() == 3)
    {
      const auto &is_sentinel_dll_expr = to_ternary_expr(what);
      auto head = evaluate_expr_rec(
        loc, state, is_sentinel_dll_expr.op0(), bound_symbols);
      auto tail = evaluate_expr_rec(
        loc, state, is_sentinel_dll_expr.op1(), bound_symbols);
      auto node = evaluate_expr_rec(
        loc, state, is_sentinel_dll_expr.op2(), bound_symbols);
      return state_is_sentinel_dll_exprt(state, head, tail, node);
    }
    else
      DATA_INVARIANT(false, "is_sentinel_dll expressions have 2 or 3 operands");
  }
  else if(what.id() == ID_side_effect)
  {
    // leave as is
    return what;
  }
  else if(
    (what.id() == ID_equal || what.id() == ID_notequal) &&
    to_binary_relation_expr(what).lhs().type().id() == ID_struct_tag)
  {
    const auto &lhs = to_binary_relation_expr(what).lhs();
    const auto &rhs = to_binary_relation_expr(what).rhs();

    const auto &type = to_struct_tag_type(lhs.type());
    const namespacet ns(goto_model.symbol_table);
    const auto &struct_type = ns.follow_tag(type);

    exprt::operandst conjuncts;

    for(auto &field : struct_type.components())
    {
      exprt lhs_member = member_exprt(lhs, field.get_name(), field.type());
      exprt rhs_member = member_exprt(rhs, field.get_name(), field.type());
      auto equality = equal_exprt(lhs_member, rhs_member);
      auto equality_evaluated =
        evaluate_expr_rec(loc, state, equality, bound_symbols);
      conjuncts.push_back(std::move(equality_evaluated));
    }

    if(what.id() == ID_equal)
      return conjunction(conjuncts);
    else
      return not_exprt(conjunction(conjuncts));
  }
  else
  {
    exprt tmp = what;
    for(auto &op : tmp.operands())
      op = evaluate_expr_rec(loc, state, op, bound_symbols);
    return tmp;
  }
}

exprt state_encodingt::evaluate_expr(loct loc, const exprt &what) const
{
  return evaluate_expr(loc, in_state_expr(loc), what);
}

exprt state_encodingt::state_lambda_expr(exprt what)
{
  return lambda_exprt({state_expr()}, std::move(what));
}

exprt state_encodingt::forall_states_expr(loct loc, exprt what) const
{
  return forall_exprt(
    {state_expr()},
    implies_exprt(
      function_application_exprt(in_state_expr(loc), {state_expr()}),
      std::move(what)));
}

exprt state_encodingt::forall_states_expr(loct loc, exprt condition, exprt what)
  const
{
  return forall_exprt(
    {state_expr()},
    implies_exprt(
      and_exprt(
        function_application_exprt(in_state_expr(loc), {state_expr()}),
        std::move(condition)),
      std::move(what)));
}

exprt state_encodingt::address_rec(loct loc, const exprt &state, exprt expr)
  const
{
  if(expr.id() == ID_symbol)
  {
    return object_address_exprt(to_symbol_expr(expr));
  }
  else if(expr.id() == ID_member)
  {
    auto compound = to_member_expr(expr).struct_op();
    auto compound_address = address_rec(loc, state, std::move(compound));
    auto component_name = to_member_expr(expr).get_component_name();

    CHECK_RETURN(compound_address.type().id() == ID_pointer);

    if(expr.type().id() == ID_array)
    {
      const auto &element_type = to_array_type(expr.type()).element_type();
      return field_address_exprt(
        std::move(compound_address),
        component_name,
        pointer_type(element_type));
    }
    else
    {
      return field_address_exprt(
        std::move(compound_address), component_name, pointer_type(expr.type()));
    }
  }
  else if(expr.id() == ID_index)
  {
    auto array = to_index_expr(expr).array();
    auto index_evaluated =
      evaluate_expr(loc, state, to_index_expr(expr).index());
    auto array_address = address_rec(loc, state, std::move(array));
    // The type of the element pointer may not be the type
    // of the base pointer, which may be a pointer to an array.
    return element_address_exprt(
      std::move(array_address),
      std::move(index_evaluated),
      pointer_type(expr.type()));
  }
  else if(expr.id() == ID_dereference)
    return evaluate_expr(loc, state, to_dereference_expr(expr).pointer());
  else if(expr.id() == ID_string_constant)
  {
    // we'll stick to 'address_of' here.
    return address_of_exprt(
      expr, pointer_type(to_array_type(expr.type()).element_type()));
  }
  else if(expr.id() == ID_array)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do array literals", expr.source_location());
  }
  else if(expr.id() == ID_struct)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do struct literals", expr.source_location());
  }
  else if(expr.id() == ID_union)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do union literals", expr.source_location());
  }
  else if(expr.id() == ID_side_effect)
  {
    // Should have been removed elsewhere.
    throw incorrect_goto_program_exceptiont(
      "address of side effect " +
        id2string(to_side_effect_expr(expr).get_statement()),
      expr.source_location());
  }
  else if(expr.id() == ID_typecast)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do assignments to typecasts", expr.source_location());
  }
  else
  {
    // address of something we don't know
    throw incorrect_goto_program_exceptiont(
      "address of unknown object " + expr.id_string(), expr.source_location());
  }
}

exprt state_encodingt::assignment_constraint_rec(
  loct loc,
  exprt state,
  exprt lhs,
  exprt rhs,
  std::vector<symbol_exprt> &nondet_symbols) const
{
  if(lhs.type().id() == ID_struct_tag)
  {
    // split up into fields, recursively
    const namespacet ns(goto_model.symbol_table);
    const auto &struct_type = ns.follow_tag(to_struct_tag_type(lhs.type()));
    exprt new_state = state;
    for(auto &field : struct_type.components())
    {
      exprt lhs_member = member_exprt(lhs, field.get_name(), field.type());
      exprt rhs_member = member_exprt(rhs, field.get_name(), field.type());

      if(rhs.id() == ID_struct)
        rhs_member = simplify_expr(rhs_member, ns);
      else if(
        rhs.id() == ID_side_effect &&
        to_side_effect_expr(rhs).get_statement() == ID_nondet)
      {
        rhs_member =
          side_effect_expr_nondett(rhs_member.type(), rhs.source_location());
      }

      new_state = assignment_constraint_rec(
        loc, new_state, lhs_member, rhs_member, nondet_symbols);
    }

    return new_state;
  }
  else if(lhs.type().id() == ID_array)
  {
    // split up into elements, recursively
    const namespacet ns(goto_model.symbol_table);
    auto &array_type = to_array_type(lhs.type());
    if(array_type.size().is_constant())
    {
      auto size_int =
        numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));
      exprt new_state = state;

      for(mp_integer i = 0; i < size_int; ++i)
      {
        auto i_expr = from_integer(i, array_type.index_type());
        exprt lhs_index = index_exprt(lhs, i_expr);
        exprt rhs_index = index_exprt(rhs, i_expr);

        if(rhs.id() == ID_array)
          rhs_index = simplify_expr(rhs_index, ns);
        else if(
          rhs.id() == ID_side_effect &&
          to_side_effect_expr(rhs).get_statement() == ID_nondet)
        {
          rhs_index =
            side_effect_expr_nondett(rhs_index.type(), rhs.source_location());
        }

        new_state = assignment_constraint_rec(
          loc, new_state, lhs_index, rhs_index, nondet_symbols);
      }

      return new_state;
    }
    else
    {
      // TODO: quantifier?
      return state;
    }
  }
  else
  {
    auto s = state_expr();
    auto address = address_rec(loc, s, lhs);

    exprt rhs_evaluated = evaluate_expr(loc, s, rhs);

    exprt new_value = replace_nondet_rec(loc, rhs_evaluated, nondet_symbols);

    return update_state_exprt(state, address, new_value);
  }
}

exprt state_encodingt::assignment_constraint(loct loc, exprt lhs, exprt rhs)
  const
{
  std::vector<symbol_exprt> nondet_symbols;

  auto new_state =
    assignment_constraint_rec(loc, state_expr(), lhs, rhs, nondet_symbols);

  forall_exprt::variablest binding = {state_expr()};
  binding.insert(binding.end(), nondet_symbols.begin(), nondet_symbols.end());

  return forall_exprt(
    std::move(binding),
    implies_exprt(
      function_application_exprt(in_state_expr(loc), {state_expr()}),
      function_application_exprt(out_state_expr(loc), {new_state})));
}

void state_encodingt::setup_incoming(const goto_functiont &goto_function)
{
  forall_goto_program_instructions(it, goto_function.body)
    incoming[it];

  forall_goto_program_instructions(it, goto_function.body)
  {
    if(it->is_goto())
      incoming[it->get_target()].push_back(it);
  }

  forall_goto_program_instructions(it, goto_function.body)
  {
    auto next = std::next(it);
    if(it->is_goto() && it->condition().is_true())
    {
    }
    else if(next != goto_function.body.instructions.end())
    {
      incoming[next].push_back(it);
    }
  }
}

static exprt simplifying_not(exprt src)
{
  if(src.id() == ID_not)
    return to_not_expr(src).op();
  else
    return not_exprt(src);
}

symbol_exprt state_encodingt::va_args(irep_idt function)
{
  return symbol_exprt(
    "va_args::" + id2string(function),
    pointer_type(pointer_type(empty_typet())));
}

std::set<irep_idt> no_body_warnings;

void state_encodingt::function_call_symbol(
  goto_programt::const_targett loc,
  encoding_targett &dest)
{
  const auto &function = to_symbol_expr(loc->call_function());
  const auto &type = to_code_type(function.type());
  auto identifier = function.get_identifier();

  auto new_annotation = annotation + u8" \u2192 " + id2string(identifier);
  dest.annotation(new_annotation);

  // malloc is special-cased
  if(identifier == "malloc")
  {
    auto state = state_expr();
    PRECONDITION(loc->call_arguments().size() == 1);
    auto size_evaluated = evaluate_expr(loc, state, loc->call_arguments()[0]);

    auto lhs_address = address_rec(loc, state, loc->call_lhs());
    auto lhs_type = to_pointer_type(loc->call_lhs().type());
    exprt new_state = update_state_exprt(
      state, lhs_address, allocate_exprt(state, size_evaluated, lhs_type));
    dest << forall_states_expr(
      loc, function_application_exprt(out_state_expr(loc), {new_state}));
    return;
  }

  // malloc is special-cased
  if(identifier == "posix_memalign")
  {
    // int posix_memalign(void **memptr, size_t alignment, size_t size);
    auto state = state_expr();
    PRECONDITION(loc->call_arguments().size() == 3);
    auto memptr_evaluated = evaluate_expr(loc, state, loc->call_arguments()[0]);
    auto size_evaluated = evaluate_expr(loc, state, loc->call_arguments()[2]);
    auto lhs_type =
      to_pointer_type(to_pointer_type(memptr_evaluated.type()).base_type());
    exprt new_state = update_state_exprt(
      state, memptr_evaluated, allocate_exprt(state, size_evaluated, lhs_type));
    dest << forall_states_expr(
      loc, function_application_exprt(out_state_expr(loc), {new_state}));
    return;
  }

  // realloc is special-cased
  if(identifier == "realloc")
  {
    auto state = state_expr();
    PRECONDITION(loc->call_arguments().size() == 2);
    auto pointer_evaluated =
      evaluate_expr(loc, state, loc->call_arguments()[0]);
    auto size_evaluated = evaluate_expr(loc, state, loc->call_arguments()[1]);

    auto lhs_address = address_rec(loc, state, loc->call_lhs());
    auto lhs_type = to_pointer_type(loc->call_lhs().type());
    exprt new_state = update_state_exprt(
      state,
      lhs_address,
      reallocate_exprt(state, pointer_evaluated, size_evaluated, lhs_type));
    dest << forall_states_expr(
      loc, function_application_exprt(out_state_expr(loc), {new_state}));
    return;
  }

  // free is special-cased
  if(identifier == "free")
  {
    auto state = state_expr();
    PRECONDITION(loc->call_arguments().size() == 1);
    auto address_evaluated =
      evaluate_expr(loc, state, loc->call_arguments()[0]);

    exprt new_state = deallocate_state_exprt(state, address_evaluated);
    dest << forall_states_expr(
      loc, function_application_exprt(out_state_expr(loc), {new_state}));
    return;
  }

  // Find the function
  auto f = goto_model.goto_functions.function_map.find(identifier);
  if(f == goto_model.goto_functions.function_map.end())
    DATA_INVARIANT(false, "failed find function in function_map");

  // Do we have a function body?
  if(!f->second.body_available())
  {
    // no function body -- do LHS assignment nondeterministically, if any
    if(loc->call_lhs().is_not_nil())
    {
      auto rhs = side_effect_expr_nondett(
        loc->call_lhs().type(), loc->source_location());
      dest << assignment_constraint(loc, loc->call_lhs(), std::move(rhs));
    }
    else
    {
      // This is a SKIP.
      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
    }

    // issue a warning, but only once
    if(no_body_warnings.insert(identifier).second)
      std::cout << "**** WARNING: no body for function " << identifier << '\n';
  }
  else
  {
    // Yes, we've got a body. Check whether this is recursive.
    if(
      std::find(call_stack.begin(), call_stack.end(), identifier) !=
      call_stack.end())
    {
      // ignore
      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      return;
    }

    // Evaluate the arguments of the call in the 'in state'
    exprt arguments_state = state_expr();
    const auto &arguments = loc->call_arguments();

    // regular parameters
    for(std::size_t i = 0; i < type.parameters().size(); i++)
    {
      auto address = object_address_exprt(symbol_exprt(
        f->second.parameter_identifiers[i], type.parameters()[i].type()));
      auto value = evaluate_expr(loc, state_expr(), arguments[i]);
      arguments_state = update_state_exprt(arguments_state, address, value);
    }

    // extra arguments, i.e., va_arg
    if(arguments.size() > type.parameters().size())
    {
      std::vector<exprt> va_args_elements;
      auto void_ptr = pointer_type(empty_typet());

      for(std::size_t i = type.parameters().size(); i < arguments.size(); i++)
      {
        auto index = i - type.parameters().size();
        auto id = "va_arg::" + state_prefix +
                  std::to_string(loc->location_number) +
                  "::" + std::to_string(index);
        auto address =
          object_address_exprt(symbol_exprt(id, arguments[i].type()));
        auto value = evaluate_expr(loc, state_expr(), arguments[i]);
        va_args_elements.push_back(
          typecast_exprt::conditional_cast(address, void_ptr));
        arguments_state = update_state_exprt(arguments_state, address, value);
      }

      // assign these to an array
      auto va_count = va_args_elements.size();
      auto array_type = array_typet(
        pointer_type(empty_typet()), from_integer(va_count, size_type()));
      auto array_identifier =
        "va_arg_array::" + state_prefix + std::to_string(loc->location_number);
      auto array_symbol = symbol_exprt(array_identifier, array_type);

      for(std::size_t i = 0; i < va_count; i++)
      {
        auto address = element_address_exprt(
          object_address_exprt(array_symbol),
          from_integer(i, array_type.index_type()),
          pointer_type(void_ptr));
        auto value = va_args_elements[i];
        arguments_state = update_state_exprt(arguments_state, address, value);
      }

      // now make va_args point to the beginning of that array
      auto address = object_address_exprt(va_args(identifier));
      auto value = element_address_exprt(
        object_address_exprt(array_symbol),
        from_integer(0, array_type.index_type()),
        pointer_type(void_ptr));
      arguments_state = update_state_exprt(arguments_state, address, value);
    }

    // Now assign all the arguments to the parameters
    auto function_entry_state = state_expr_with_suffix(loc, "Entry");
    dest << forall_states_expr(
      loc, function_application_exprt(function_entry_state, {arguments_state}));

    // now do the body, recursively
    state_encodingt body_state_encoding(goto_model);
    auto new_state_prefix =
      state_prefix + std::to_string(loc->location_number) + ".";
    auto new_call_stack = call_stack;
    new_call_stack.push_back(function_identifier);
    body_state_encoding.encode(
      f->second,
      identifier,
      new_state_prefix,
      new_call_stack,
      new_annotation,
      function_entry_state,
      nil_exprt(),
      dest);

    // exit state of called function
    auto exit_loc = std::prev(f->second.body.instructions.end());
    irep_idt exit_state_identifier =
      new_state_prefix + std::to_string(exit_loc->location_number);
    auto exit_state =
      symbol_exprt(exit_state_identifier, state_predicate_type());

    // done with function, reset source location to call site
    dest.set_source_location(loc->source_location());

    // now assign the return value, if any
    if(loc->call_lhs().is_not_nil())
    {
      auto rhs = symbol_exprt("return_value", loc->call_lhs().type());
      auto state = state_expr();
      auto address = address_rec(exit_loc, state, loc->call_lhs());
      auto rhs_evaluated = evaluate_expr(exit_loc, state, rhs);
      exprt new_state = update_state_exprt(state, address, rhs_evaluated);
      dest << forall_exprt(
        {state_expr()},
        implies_exprt(
          function_application_exprt(std::move(exit_state), {state_expr()}),
          function_application_exprt(out_state_expr(loc), {new_state})));
    }
    else
    {
      // link up return state to exit state
      dest << equal_exprt(out_state_expr(loc), std::move(exit_state));
    }
  }
}

void state_encodingt::function_call(
  goto_programt::const_targett loc,
  encoding_targett &dest)
{
  // Function pointer?
  const auto &function = loc->call_function();
  if(function.id() == ID_dereference)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do function pointers", loc->source_location());
  }
  else if(function.id() == ID_symbol)
  {
    function_call_symbol(loc, dest);
  }
  else
  {
    DATA_INVARIANT(
      false, "got function that's neither a symbol nor a function pointer");
  }
}

void state_encodingt::operator()(
  goto_functionst::function_mapt::const_iterator f_entry,
  encoding_targett &dest)
{
  const auto &goto_function = f_entry->second;

  if(goto_function.body.instructions.empty())
    return;

  // initial state
  auto in_state = symbol_exprt("SInitial", state_predicate_type());

  dest << forall_exprt(
    {state_expr()},
    implies_exprt(
      initial_state_exprt(state_expr()),
      function_application_exprt(in_state, {state_expr()})));

  auto annotation = id2string(f_entry->first);

  encode(
    goto_function,
    f_entry->first,
    "S",
    {},
    annotation,
    in_state,
    nil_exprt(),
    dest);
}

void state_encodingt::encode(
  const goto_functiont &goto_function,
  const irep_idt function_identifier,
  const std::string &state_prefix,
  const std::vector<irep_idt> &call_stack,
  const std::string &annotation,
  const symbol_exprt &entry_state,
  const exprt &return_lhs,
  encoding_targett &dest)
{
  first_loc = goto_function.body.instructions.begin();
  this->function_identifier = function_identifier;
  this->state_prefix = state_prefix;
  this->call_stack = call_stack;
  this->annotation = annotation;
  this->entry_state = entry_state;
  this->return_lhs = return_lhs;

  setup_incoming(goto_function);

  // constraints for each instruction
  forall_goto_program_instructions(loc, goto_function.body)
  {
    // pass on the source code location
    dest.set_source_location(loc->source_location());

    // constraints on the incoming state
    {
      auto incoming_symbols = this->incoming_symbols(loc);

      if(incoming_symbols.size() >= 2)
      {
        auto s = state_expr();
        for(auto incoming_symbol : incoming_symbols)
        {
          dest << forall_exprt(
            {s},
            implies_exprt(
              function_application_exprt(incoming_symbol, {s}),
              function_application_exprt(in_state_expr(loc), {s})));
        }
      }
    }

    if(loc->is_assign())
    {
      auto &lhs = loc->assign_lhs();
      auto &rhs = loc->assign_rhs();

      DATA_INVARIANT(lhs.type() == rhs.type(), "assignment type consistency");

      if(
        lhs.id() == ID_symbol &&
        has_prefix(
          id2string(to_symbol_expr(lhs).get_identifier()), CPROVER_PREFIX) &&
        to_symbol_expr(lhs).get_identifier() != CPROVER_PREFIX "rounding_mode")
      {
        // skip for now
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else if(
        lhs.id() == ID_symbol &&
        to_symbol_expr(lhs).get_identifier() == "_DefaultRuneLocale")
      {
        // /Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/usr/include/runetype.h
        // skip for now
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else
        dest << assignment_constraint(loc, lhs, rhs);
    }
    else if(loc->is_assume())
    {
      // we produce ∅ when the assumption is false
      auto state = state_expr();
      auto condition_evaluated = evaluate_expr(loc, state, loc->condition());

      dest << forall_states_expr(
        loc,
        condition_evaluated,
        function_application_exprt(out_state_expr(loc), {state}));
    }
    else if(loc->is_goto())
    {
      // We produce ∅ when the 'other' branch is taken. Get the condition.
      const auto &condition = loc->condition();

      if(condition.is_true())
      {
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else
      {
        auto state = state_expr();
        auto condition_evaluated = evaluate_expr(loc, state, condition);

        dest << forall_states_expr(
          loc,
          condition_evaluated,
          function_application_exprt(out_state_expr(loc, true), {state}));

        dest << forall_states_expr(
          loc,
          simplifying_not(condition_evaluated),
          function_application_exprt(out_state_expr(loc, false), {state}));
      }
    }
    else if(loc->is_assert())
    {
      // all assertions need to hold
      dest << forall_states_expr(
        loc, evaluate_expr(loc, state_expr(), loc->condition()));

      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
    }
    else if(
      loc->is_skip() || loc->is_assert() || loc->is_location() ||
      loc->is_end_function())
    {
      // these do not change the state
      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
    }
    else if(loc->is_atomic_begin() || loc->is_atomic_end())
    {
      // no concurrency yet
      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
    }
    else if(loc->is_other())
    {
      auto &code = loc->code();
      auto &statement = code.get_statement();
      if(statement == ID_array_set)
      {
        DATA_INVARIANT(
          code.operands().size() == 2, "array_set has two operands");
        // op0 must be an array
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else
      {
        // ought to print a warning
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
    }
    else if(loc->is_decl())
    {
      auto s_in = state_expr();
      auto s_out = enter_scope_state_exprt(
        s_in, address_rec(loc, s_in, loc->decl_symbol()));
      dest << forall_states_expr(
        loc, function_application_exprt(out_state_expr(loc), {s_out}));
    }
    else if(loc->is_dead())
    {
      auto s = state_expr();
      auto s_in = state_expr();
      auto s_out = exit_scope_state_exprt(
        s_in, address_rec(loc, s_in, loc->dead_symbol()));
      dest << forall_states_expr(
        loc, function_application_exprt(out_state_expr(loc), {s_out}));
    }
    else if(loc->is_function_call())
    {
      function_call(loc, dest);
    }
    else if(loc->is_set_return_value())
    {
      const auto &rhs = loc->return_value();

      if(return_lhs.is_nil())
      {
        // treat these as assignments to a special symbol named 'return_value'
        auto lhs = symbol_exprt("return_value", rhs.type());
        dest << assignment_constraint(loc, std::move(lhs), std::move(rhs));
      }
      else
      {
      }
    }
    else
    {
      std::cout << "X: " << loc->type() << '\n';
      DATA_INVARIANT(false, "unexpected GOTO instruction");
    }
  }
}

void state_encoding(
  const goto_modelt &goto_model,
  bool program_is_inlined,
  optionalt<irep_idt> contract,
  encoding_targett &dest)
{
  if(program_is_inlined)
  {
    auto f_entry = goto_model.goto_functions.function_map.find(
      goto_functionst::entry_point());

    if(f_entry == goto_model.goto_functions.function_map.end())
      throw incorrect_goto_program_exceptiont("The program has no entry point");

    dest.annotation("function " + id2string(f_entry->first));

    state_encodingt{goto_model}(f_entry, dest);
  }
  else if(contract.has_value())
  {
    // check given contract
    const namespacet ns(goto_model.symbol_table);
    const symbolt *symbol;
    if(ns.lookup(*contract, symbol))
      throw invalid_command_line_argument_exceptiont(
        "The given function was not found", "contract");

    if(!get_contract(*contract, ns).has_value())
      throw invalid_command_line_argument_exceptiont(
        "The given function has no contract", "contract");

    const auto f = goto_model.goto_functions.function_map.find(symbol->name);
    CHECK_RETURN(f != goto_model.goto_functions.function_map.end());

    dest.annotation("");
    dest.annotation("function " + id2string(symbol->name));
    state_encodingt{goto_model}(f, dest);
  }
  else
  {
    // sort alphabetically
    const auto sorted = goto_model.goto_functions.sorted();
    const namespacet ns(goto_model.symbol_table);
    bool found = false;
    for(auto &f : sorted)
    {
      if(
        f->first == goto_functionst::entry_point() ||
        get_contract(f->first, ns).has_value())
      {
        dest.annotation("");
        dest.annotation("function " + id2string(f->first));
        state_encodingt{goto_model}(f, dest);
        found = true;
      }
    }

    if(!found)
      throw incorrect_goto_program_exceptiont("The program has no entry point");
  }
}

void state_encoding(
  const goto_modelt &goto_model,
  state_encoding_formatt state_encoding_format,
  bool program_is_inlined,
  optionalt<irep_idt> contract,
  std::ostream &out)
{
  switch(state_encoding_format)
  {
  case state_encoding_formatt::ASCII:
  {
    ascii_encoding_targett dest(out);
    state_encoding(goto_model, program_is_inlined, contract, dest);
  }
  break;

  case state_encoding_formatt::SMT2:
  {
    const namespacet ns(goto_model.symbol_table);
    smt2_encoding_targett dest(ns, out);
    state_encoding(goto_model, program_is_inlined, contract, dest);
  }
  break;
  }
}

void variable_encoding(
  const goto_modelt &goto_model,
  state_encoding_formatt state_encoding_format,
  std::ostream &out)
{
  const namespacet ns(goto_model.symbol_table);

  container_encoding_targett container;
  state_encoding(goto_model, true, {}, container);

  equality_propagation(container.constraints);

  variable_encoding(container.constraints);

  switch(state_encoding_format)
  {
  case state_encoding_formatt::ASCII:
  {
    ascii_encoding_targett dest(out);
    dest << container;
  }
  break;

  case state_encoding_formatt::SMT2:
  {
    smt2_encoding_targett dest(ns, out);
    dest << container;
  }
  break;
  }
}

solver_resultt state_encoding_solver(
  const goto_modelt &goto_model,
  bool program_is_inlined,
  optionalt<irep_idt> contract,
  const solver_optionst &solver_options)
{
  const namespacet ns(goto_model.symbol_table);

  container_encoding_targett container;
  state_encoding(goto_model, program_is_inlined, contract, container);

  equality_propagation(container.constraints);

  if(solver_options.verbose)
  {
    ascii_encoding_targett dest(std::cout);
    dest << container;
  }

  return solver(container.constraints, solver_options, ns);
}

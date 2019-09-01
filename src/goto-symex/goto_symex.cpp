/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include "expr_skeleton.h"
#include "symex_assign.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/fresh_symbol.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/string_expr.h>
#include <util/string_utils.h>

#include <climits>

unsigned goto_symext::dynamic_counter=0;

void goto_symext::do_simplify(exprt &expr)
{
  if(symex_config.simplify_opt)
    simplify(expr, ns);
}

void goto_symext::symex_assign(statet &state, const code_assignt &code)
{
  exprt lhs = clean_expr(code.lhs(), state, true);
  exprt rhs = clean_expr(code.rhs(), state, false);

  DATA_INVARIANT(
    lhs.type() == rhs.type(), "assignments must be type consistent");

  log.conditional_output(
    log.debug(), [this, &lhs](messaget::mstreamt &mstream) {
      mstream << "Assignment to " << format(lhs) << " ["
              << pointer_offset_bits(lhs.type(), ns).value_or(0) << " bits]"
              << messaget::eom;
    });

  // rvalues present within the lhs (for example, "some_array[this_rvalue]" or
  // "byte_extract <type> from an_lvalue offset this_rvalue") can affect whether
  // we use field-sensitive symbols or not, so L2-rename them up front:
  lhs = state.l2_rename_rvalues(lhs, ns);
  do_simplify(lhs);
  lhs = state.field_sensitivity.apply(ns, state, std::move(lhs), true);

  if(rhs.id() == ID_side_effect)
  {
    const side_effect_exprt &side_effect_expr = to_side_effect_expr(rhs);
    const irep_idt &statement = side_effect_expr.get_statement();

    if(
      statement == ID_cpp_new || statement == ID_cpp_new_array ||
      statement == ID_java_new_array_data)
    {
      symex_cpp_new(state, lhs, side_effect_expr);
    }
    else if(statement == ID_allocate)
      symex_allocate(state, lhs, side_effect_expr);
    else if(statement == ID_va_start)
      symex_va_start(state, lhs, side_effect_expr);
    else
      UNREACHABLE;
  }
  else
  {
    assignment_typet assignment_type = symex_targett::assignment_typet::STATE;

    // Let's hide return value assignments.
    if(
      lhs.id() == ID_symbol &&
      id2string(to_symbol_expr(lhs).get_identifier()).find("#return_value!") !=
        std::string::npos)
    {
      assignment_type = symex_targett::assignment_typet::HIDDEN;
    }

    // We hide if we are in a hidden function.
    if(state.call_stack().top().hidden_function)
      assignment_type = symex_targett::assignment_typet::HIDDEN;

    // We hide if we are executing a hidden instruction.
    if(state.source.pc->source_location.get_hide())
      assignment_type = symex_targett::assignment_typet::HIDDEN;

    symex_assignt symex_assign{
      state, assignment_type, ns, symex_config, target};

    // Try to constant propagate potential side effects of the assignment, when
    // simplification is turned on and there is one thread only. Constant
    // propagation is only sound for sequential code as here we do not take into
    // account potential writes from other threads when propagating the values.
    if(symex_config.simplify_opt && state.threads.size() <= 1)
    {
      if(constant_propagate_assignment_with_side_effects(
           state, symex_assign, lhs, rhs))
        return;
    }

    exprt::operandst lhs_if_then_else_conditions;
    symex_assign.assign_rec(
      lhs, expr_skeletont{}, rhs, lhs_if_then_else_conditions);
  }
}

/// Maps the given array expression containing constant characters to a string
/// containing only alphanumeric characters
///
/// \param char_array: array_exprt containing characters represented by
///   expressions of kind constant_exprt and type unsignedbv_typet or
///   signedbv_typet
/// \return a string containing only alphanumeric characters
static std::string get_alnum_string(const array_exprt &char_array)
{
  const auto &ibv_type =
    to_integer_bitvector_type(to_array_type(char_array.type()).subtype());

  const std::size_t n_bits = ibv_type.get_width();
  CHECK_RETURN(n_bits % 8 == 0);

  static_assert(CHAR_BIT == 8, "bitwidth of char assumed to be 8");

  const std::size_t n_chars = n_bits / 8;

  INVARIANT(
    sizeof(std::size_t) >= n_chars,
    "size_t shall be large enough to represent a character");

  std::string result;

  for(const auto &c : char_array.operands())
  {
    const std::size_t c_val = numeric_cast_v<std::size_t>(to_constant_expr(c));

    for(std::size_t i = 0; i < n_chars; i++)
    {
      const char c_chunk = static_cast<char>((c_val >> (i * 8)) & 0xff);
      result.push_back(c_chunk);
    }
  }

  return escape_non_alnum(result);
}

bool goto_symext::constant_propagate_assignment_with_side_effects(
  statet &state,
  symex_assignt &symex_assign,
  const exprt &lhs,
  const exprt &rhs)
{
  if(rhs.id() == ID_function_application)
  {
    const function_application_exprt &f_l1 = to_function_application_expr(rhs);

    if(f_l1.function().id() == ID_symbol)
    {
      const irep_idt &func_id =
        to_symbol_expr(f_l1.function()).get_identifier();

      if(func_id == ID_cprover_string_concat_func)
      {
        return constant_propagate_string_concat(state, symex_assign, f_l1);
      }
      else if(func_id == ID_cprover_string_empty_string_func)
      {
        // constant propagating the empty string always succeeds as it does
        // not depend on potentially non-constant inputs
        constant_propagate_empty_string(state, symex_assign, f_l1);
        return true;
      }
      else if(func_id == ID_cprover_string_substring_func)
      {
        return constant_propagate_string_substring(state, symex_assign, f_l1);
      }
      else if(
        func_id == ID_cprover_string_of_int_func ||
        func_id == ID_cprover_string_of_long_func)
      {
        return constant_propagate_integer_to_string(state, symex_assign, f_l1);
      }
    }
  }

  return false;
}

void goto_symext::assign_string_constant(
  statet &state,
  symex_assignt &symex_assign,
  const ssa_exprt &length,
  const constant_exprt &new_length,
  const ssa_exprt &char_array,
  const array_exprt &new_char_array)
{
  // We need to make sure that the length of the previous array isn't
  // unconstrained, otherwise it could be arbitrarily large which causes
  // invalid traces
  symex_assume(state, equal_exprt{length, from_integer(0, length.type())});

  // assign length of string
  symex_assign.assign_symbol(length, expr_skeletont{}, new_length, {});

  const std::string aux_symbol_name =
    get_alnum_string(new_char_array) + "_constant_char_array";

  const bool string_constant_exists =
    state.symbol_table.has_symbol(aux_symbol_name);

  const symbolt &aux_symbol =
    string_constant_exists
      ? state.symbol_table.lookup_ref(aux_symbol_name)
      : get_new_string_data_symbol(
          state, symex_assign, aux_symbol_name, char_array, new_char_array);

  INVARIANT(
    aux_symbol.value == new_char_array,
    "symbol shall have value derived from char array content");

  const address_of_exprt string_data(
    index_exprt(aux_symbol.symbol_expr(), from_integer(0, index_type())));

  symex_assign.assign_symbol(char_array, expr_skeletont{}, string_data, {});

  if(!string_constant_exists)
  {
    associate_array_to_pointer(
      state, symex_assign, new_char_array, string_data);
  }
}

const symbolt &goto_symext::get_new_string_data_symbol(
  statet &state,
  symex_assignt &symex_assign,
  const std::string &aux_symbol_name,
  const ssa_exprt &char_array,
  const array_exprt &new_char_array)
{
  array_typet new_char_array_type = new_char_array.type();
  new_char_array_type.set(ID_C_constant, true);

  symbolt &new_aux_symbol = get_fresh_aux_symbol(
    new_char_array_type,
    "",
    aux_symbol_name,
    source_locationt(),
    ns.lookup(to_symbol_expr(char_array.get_original_expr())).mode,
    ns,
    state.symbol_table);

  CHECK_RETURN(new_aux_symbol.is_state_var);
  CHECK_RETURN(new_aux_symbol.is_lvalue);

  new_aux_symbol.is_static_lifetime = true;
  new_aux_symbol.is_file_local = false;
  new_aux_symbol.is_thread_local = false;

  new_aux_symbol.value = new_char_array;

  const exprt arr = state.rename(new_aux_symbol.symbol_expr(), ns).get();

  symex_assign.assign_symbol(
    to_ssa_expr(arr).get_l1_object(), expr_skeletont{}, new_char_array, {});

  return new_aux_symbol;
}

void goto_symext::associate_array_to_pointer(
  statet &state,
  symex_assignt &symex_assign,
  const array_exprt &new_char_array,
  const address_of_exprt &string_data)
{
  const symbolt &function_symbol =
    ns.lookup(ID_cprover_associate_array_to_pointer_func);

  const function_application_exprt array_to_pointer_app{
    function_symbol.symbol_expr(), {new_char_array, string_data}};

  const symbolt &return_symbol = get_fresh_aux_symbol(
    to_mathematical_function_type(function_symbol.type).codomain(),
    "",
    "return_value",
    source_locationt(),
    function_symbol.mode,
    ns,
    state.symbol_table);

  const ssa_exprt ssa_expr(return_symbol.symbol_expr());

  symex_assign.assign_symbol(
    ssa_expr, expr_skeletont{}, array_to_pointer_app, {});
}

optionalt<std::reference_wrapper<const array_exprt>>
goto_symext::try_evaluate_constant_string(
  const statet &state,
  const exprt &content)
{
  if(content.id() != ID_symbol)
  {
    return {};
  }

  const auto s_pointer_opt =
    state.propagation.find(to_symbol_expr(content).get_identifier());

  if(!s_pointer_opt)
  {
    return {};
  }

  return try_get_string_data_array(s_pointer_opt->get(), ns);
}

optionalt<std::reference_wrapper<const constant_exprt>>
goto_symext::try_evaluate_constant(const statet &state, const exprt &expr)
{
  if(expr.id() != ID_symbol)
  {
    return {};
  }

  const auto constant_expr_opt =
    state.propagation.find(to_symbol_expr(expr).get_identifier());

  if(!constant_expr_opt || constant_expr_opt->get().id() != ID_constant)
  {
    return {};
  }

  return optionalt<std::reference_wrapper<const constant_exprt>>(
    to_constant_expr(constant_expr_opt->get()));
}

void goto_symext::constant_propagate_empty_string(
  statet &state,
  symex_assignt &symex_assign,
  const function_application_exprt &f_l1)
{
  const auto &f_type = to_mathematical_function_type(f_l1.function().type());
  const auto &length_type = f_type.domain().at(0);
  const auto &char_type = to_pointer_type(f_type.domain().at(1)).subtype();

  const constant_exprt length = from_integer(0, length_type);

  const array_typet char_array_type(char_type, length);

  DATA_INVARIANT(
    f_l1.arguments().size() == 2,
    "empty string primitive takes two output arguments");

  const array_exprt char_array({}, char_array_type);

  assign_string_constant(
    state,
    symex_assign,
    to_ssa_expr(f_l1.arguments().at(0)),
    length,
    to_ssa_expr(f_l1.arguments().at(1)),
    char_array);
}

bool goto_symext::constant_propagate_string_concat(
  statet &state,
  symex_assignt &symex_assign,
  const function_application_exprt &f_l1)
{
  const auto &f_type = to_mathematical_function_type(f_l1.function().type());
  const auto &length_type = f_type.domain().at(0);
  const auto &char_type = to_pointer_type(f_type.domain().at(1)).subtype();

  const refined_string_exprt &s1 = to_string_expr(f_l1.arguments().at(2));
  const auto s1_data_opt = try_evaluate_constant_string(state, s1.content());

  if(!s1_data_opt)
    return false;

  const array_exprt &s1_data = s1_data_opt->get();

  const refined_string_exprt &s2 = to_string_expr(f_l1.arguments().at(3));
  const auto s2_data_opt = try_evaluate_constant_string(state, s2.content());

  if(!s2_data_opt)
    return false;

  const array_exprt &s2_data = s2_data_opt->get();

  const std::size_t new_size =
    s1_data.operands().size() + s2_data.operands().size();

  const constant_exprt new_char_array_length =
    from_integer(new_size, length_type);

  const array_typet new_char_array_type(char_type, new_char_array_length);

  exprt::operandst operands(s1_data.operands());
  operands.insert(
    operands.end(), s2_data.operands().begin(), s2_data.operands().end());

  const array_exprt new_char_array(std::move(operands), new_char_array_type);

  assign_string_constant(
    state,
    symex_assign,
    to_ssa_expr(f_l1.arguments().at(0)),
    new_char_array_length,
    to_ssa_expr(f_l1.arguments().at(1)),
    new_char_array);

  return true;
}

bool goto_symext::constant_propagate_string_substring(
  statet &state,
  symex_assignt &symex_assign,
  const function_application_exprt &f_l1)
{
  const std::size_t num_operands = f_l1.arguments().size();

  PRECONDITION(num_operands >= 4);
  PRECONDITION(num_operands <= 5);

  const auto &f_type = to_mathematical_function_type(f_l1.function().type());
  const auto &length_type = f_type.domain().at(0);
  const auto &char_type = to_pointer_type(f_type.domain().at(1)).subtype();

  const refined_string_exprt &s = to_string_expr(f_l1.arguments().at(2));
  const auto s_data_opt = try_evaluate_constant_string(state, s.content());

  if(!s_data_opt)
    return false;

  const array_exprt &s_data = s_data_opt->get();

  mp_integer end_index;

  if(num_operands == 5)
  {
    const auto end_index_expr_opt =
      try_evaluate_constant(state, f_l1.arguments().at(4));

    if(!end_index_expr_opt)
    {
      return false;
    }

    end_index =
      numeric_cast_v<mp_integer>(to_constant_expr(*end_index_expr_opt));

    if(end_index < 0 || end_index > s_data.operands().size())
    {
      return false;
    }
  }
  else
  {
    end_index = s_data.operands().size();
  }

  const auto start_index_expr_opt =
    try_evaluate_constant(state, f_l1.arguments().at(3));

  if(!start_index_expr_opt)
  {
    return false;
  }

  const mp_integer start_index =
    numeric_cast_v<mp_integer>(to_constant_expr(*start_index_expr_opt));

  if(start_index < 0 || start_index > end_index)
  {
    return false;
  }

  const constant_exprt new_char_array_length =
    from_integer(end_index - start_index, length_type);

  const array_typet new_char_array_type(char_type, new_char_array_length);

  exprt::operandst operands(
    std::next(
      s_data.operands().begin(), numeric_cast_v<std::size_t>(start_index)),
    std::next(
      s_data.operands().begin(), numeric_cast_v<std::size_t>(end_index)));

  const array_exprt new_char_array(std::move(operands), new_char_array_type);

  assign_string_constant(
    state,
    symex_assign,
    to_ssa_expr(f_l1.arguments().at(0)),
    new_char_array_length,
    to_ssa_expr(f_l1.arguments().at(1)),
    new_char_array);

  return true;
}

bool goto_symext::constant_propagate_integer_to_string(
  statet &state,
  symex_assignt &symex_assign,
  const function_application_exprt &f_l1)
{
  // The function application expression f_l1 takes the following arguments:
  // - result string length (output parameter)
  // - result string data array (output parameter)
  // - integer to convert to a string
  // - radix (optional, default 10)
  const std::size_t num_operands = f_l1.arguments().size();

  PRECONDITION(num_operands >= 3);
  PRECONDITION(num_operands <= 4);

  const auto &f_type = to_mathematical_function_type(f_l1.function().type());
  const auto &length_type = f_type.domain().at(0);
  const auto &char_type = to_pointer_type(f_type.domain().at(1)).subtype();

  const auto &integer_opt =
    try_evaluate_constant(state, f_l1.arguments().at(2));

  if(!integer_opt)
  {
    return false;
  }

  const mp_integer integer = numeric_cast_v<mp_integer>(integer_opt->get());

  unsigned base = 10;

  if(num_operands == 4)
  {
    const auto &base_constant_opt =
      try_evaluate_constant(state, f_l1.arguments().at(3));

    if(!base_constant_opt)
    {
      return false;
    }

    const auto base_opt = numeric_cast<unsigned>(base_constant_opt->get());

    if(!base_opt)
    {
      return false;
    }

    base = *base_opt;
  }

  std::string s = integer2string(integer, base);

  const constant_exprt new_char_array_length =
    from_integer(s.length(), length_type);

  const array_typet new_char_array_type(char_type, new_char_array_length);

  exprt::operandst operands;

  std::transform(
    s.begin(),
    s.end(),
    std::back_inserter(operands),
    [&char_type](const char c) { return from_integer(tolower(c), char_type); });

  const array_exprt new_char_array(std::move(operands), new_char_array_type);

  assign_string_constant(
    state,
    symex_assign,
    to_ssa_expr(f_l1.arguments().at(0)),
    new_char_array_length,
    to_ssa_expr(f_l1.arguments().at(1)),
    new_char_array);

  return true;
}

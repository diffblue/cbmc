/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "goto_symex.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/invariant_utils.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/string_constant.h>

#include "path_storage.h"

inline static optionalt<typet> c_sizeof_type_rec(const exprt &expr)
{
  const irept &sizeof_type=expr.find(ID_C_c_sizeof_type);

  if(!sizeof_type.is_nil())
  {
    return static_cast<const typet &>(sizeof_type);
  }
  else if(expr.id()==ID_mult)
  {
    forall_operands(it, expr)
    {
      const auto t = c_sizeof_type_rec(*it);
      if(t.has_value())
        return t;
    }
  }

  return {};
}

void goto_symext::symex_allocate(
  statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  PRECONDITION(code.operands().size() == 2);

  if(lhs.is_nil())
    return; // ignore

  dynamic_counter++;

  exprt size = to_binary_expr(code).op0();
  optionalt<typet> object_type;
  auto function_symbol = outer_symbol_table.lookup(state.source.function_id);
  INVARIANT(function_symbol, "function associated with allocation not found");
  const irep_idt &mode = function_symbol->mode;

  // is the type given?
  if(
    code.type().id() == ID_pointer &&
    to_pointer_type(code.type()).subtype().id() != ID_empty)
  {
    object_type = to_pointer_type(code.type()).subtype();
  }
  else
  {
    // to allow constant propagation
    exprt tmp_size = state.rename(size, ns).get();
    simplify(tmp_size, ns);

    // special treatment for sizeof(T)*x
    {
      const auto tmp_type = c_sizeof_type_rec(tmp_size);

      if(tmp_type.has_value())
      {
        // Did the size get multiplied?
        auto elem_size = pointer_offset_size(*tmp_type, ns);
        const auto alloc_size = numeric_cast<mp_integer>(tmp_size);

        if(!elem_size.has_value() || *elem_size==0)
        {
        }
        else if(
          !alloc_size.has_value() && tmp_size.id() == ID_mult &&
          tmp_size.operands().size() == 2 &&
          (to_mult_expr(tmp_size).op0().is_constant() ||
           to_mult_expr(tmp_size).op1().is_constant()))
        {
          exprt s = to_mult_expr(tmp_size).op0();
          if(s.is_constant())
          {
            s = to_mult_expr(tmp_size).op1();
            PRECONDITION(
              *c_sizeof_type_rec(to_mult_expr(tmp_size).op0()) == *tmp_type);
          }
          else
            PRECONDITION(
              *c_sizeof_type_rec(to_mult_expr(tmp_size).op1()) == *tmp_type);

          object_type = array_typet(*tmp_type, s);
        }
        else if(alloc_size.has_value())
        {
          if(*alloc_size == *elem_size)
            object_type = *tmp_type;
          else
          {
            mp_integer elements = *alloc_size / (*elem_size);

            if(elements * (*elem_size) == *alloc_size)
              object_type =
                array_typet(*tmp_type, from_integer(elements, tmp_size.type()));
          }
        }
      }
    }

    if(!object_type.has_value())
      object_type=array_typet(unsigned_char_type(), tmp_size);

    // we introduce a fresh symbol for the size
    // to prevent any issues of the size getting ever changed

    if(
      object_type->id() == ID_array &&
      !to_array_type(*object_type).size().is_constant())
    {
      exprt &array_size = to_array_type(*object_type).size();

      auxiliary_symbolt size_symbol;

      size_symbol.base_name=
        "dynamic_object_size"+std::to_string(dynamic_counter);
      size_symbol.name =
        SYMEX_DYNAMIC_PREFIX + id2string(size_symbol.base_name);
      size_symbol.type=tmp_size.type();
      size_symbol.mode = mode;
      size_symbol.type.set(ID_C_constant, true);
      size_symbol.value = array_size;

      state.symbol_table.add(size_symbol);

      auto array_size_rhs = array_size;
      array_size = size_symbol.symbol_expr();

      symex_assign(state, size_symbol.symbol_expr(), array_size_rhs);
    }
  }

  // value
  symbolt value_symbol;

  value_symbol.base_name="dynamic_object"+std::to_string(dynamic_counter);
  value_symbol.name = SYMEX_DYNAMIC_PREFIX + id2string(value_symbol.base_name);
  value_symbol.is_lvalue=true;
  value_symbol.type = *object_type;
  value_symbol.type.set(ID_C_dynamic, true);
  value_symbol.mode = mode;

  state.symbol_table.add(value_symbol);

  // to allow constant propagation
  exprt zero_init = state.rename(to_binary_expr(code).op1(), ns).get();
  simplify(zero_init, ns);

  INVARIANT(
    zero_init.is_constant(), "allocate expects constant as second argument");

  if(!zero_init.is_zero() && !zero_init.is_false())
  {
    const auto zero_value =
      zero_initializer(*object_type, code.source_location(), ns);
    CHECK_RETURN(zero_value.has_value());
    symex_assign(state, value_symbol.symbol_expr(), *zero_value);
  }
  else
  {
    auto lhs = value_symbol.symbol_expr();
    auto rhs =
      path_storage.build_symex_nondet(*object_type, code.source_location());
    symex_assign(state, lhs, rhs);
  }

  exprt rhs;

  if(object_type->id() == ID_array)
  {
    const auto &array_type = to_array_type(*object_type);
    index_exprt index_expr(
      value_symbol.symbol_expr(), from_integer(0, index_type()));
    rhs = address_of_exprt(index_expr, pointer_type(array_type.subtype()));
  }
  else
  {
    rhs=address_of_exprt(
      value_symbol.symbol_expr(), pointer_type(value_symbol.type));
  }

  symex_assign(state, lhs, typecast_exprt::conditional_cast(rhs, lhs.type()));
}

/// Construct an entry for the var args array. Visual Studio complicates this as
/// we need to put immediate values or pointers in there, depending on the size
/// of the parameter.
static exprt va_list_entry(
  const irep_idt &parameter,
  const pointer_typet &lhs_type,
  const namespacet &ns)
{
  static const pointer_typet void_ptr_type = pointer_type(empty_typet{});

  symbol_exprt parameter_expr = ns.lookup(parameter).symbol_expr();

  // Visual Studio has va_list == char* and stores parameters of size no
  // greater than the size of a pointer as immediate values
  if(lhs_type.subtype().id() != ID_pointer)
  {
    auto parameter_size = size_of_expr(parameter_expr.type(), ns);
    CHECK_RETURN(parameter_size.has_value());

    binary_predicate_exprt fits_slot{
      *parameter_size,
      ID_le,
      from_integer(lhs_type.get_width(), parameter_size->type())};

    return if_exprt{
      fits_slot,
      typecast_exprt::conditional_cast(parameter_expr, void_ptr_type),
      typecast_exprt::conditional_cast(
        address_of_exprt{parameter_expr}, void_ptr_type)};
  }
  else
  {
    return typecast_exprt::conditional_cast(
      address_of_exprt{std::move(parameter_expr)}, void_ptr_type);
  }
}

void goto_symext::symex_va_start(
  statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  PRECONDITION(code.operands().size() == 1);

  if(lhs.is_nil())
    return; // ignore

  // create an array holding pointers to the parameters, starting after the
  // parameter that the operand points to
  const exprt &op = skip_typecast(to_unary_expr(code).op());
  // this must be the address of a symbol
  const irep_idt start_parameter =
    to_ssa_expr(to_address_of_expr(op).object()).get_object_name();

  exprt::operandst va_arg_operands;
  bool parameter_id_found = false;
  for(auto &parameter : state.call_stack().top().parameter_names)
  {
    if(!parameter_id_found)
    {
      parameter_id_found = parameter == start_parameter;
      continue;
    }

    va_arg_operands.push_back(
      va_list_entry(parameter, to_pointer_type(lhs.type()), ns));
  }
  const std::size_t va_arg_size = va_arg_operands.size();
  exprt array =
    array_exprt{std::move(va_arg_operands),
                array_typet{pointer_type(empty_typet{}),
                            from_integer(va_arg_size, size_type())}};

  symbolt &va_array = get_fresh_aux_symbol(
    array.type(),
    id2string(state.source.function_id),
    "va_args",
    state.source.pc->source_location(),
    ns.lookup(state.source.function_id).mode,
    state.symbol_table);
  va_array.value = array;

  array = clean_expr(std::move(array), state, false);
  array = state.rename(std::move(array), ns).get();
  do_simplify(array);
  symex_assign(state, va_array.symbol_expr(), std::move(array));

  exprt rhs = address_of_exprt{
    index_exprt{va_array.symbol_expr(), from_integer(0, index_type())}};
  rhs = state.rename(std::move(rhs), ns).get();
  symex_assign(state, lhs, typecast_exprt::conditional_cast(rhs, lhs.type()));
}

static irep_idt get_string_argument_rec(const exprt &src)
{
  if(src.id()==ID_typecast)
  {
    return get_string_argument_rec(to_typecast_expr(src).op());
  }
  else if(src.id()==ID_address_of)
  {
    const exprt &object = to_address_of_expr(src).object();

    if(object.id() == ID_index)
    {
      const auto &index_expr = to_index_expr(object);

      if(
        index_expr.array().id() == ID_string_constant &&
        index_expr.index().is_zero())
      {
        const exprt &fmt_str = index_expr.array();
        return to_string_constant(fmt_str).get_value();
      }
    }
    else if(object.id() == ID_string_constant)
    {
      return to_string_constant(object).get_value();
    }
  }

  return irep_idt();
}

static irep_idt get_string_argument(const exprt &src, const namespacet &ns)
{
  exprt tmp=src;
  simplify(tmp, ns);
  return get_string_argument_rec(tmp);
}

/// Return an expression if \p operands fulfills all criteria that we expect of
/// the expression to be a variable argument list.
static optionalt<exprt> get_va_args(const exprt::operandst &operands)
{
  if(operands.size() != 2)
    return {};

  const exprt &second_op = skip_typecast(operands.back());
  if(second_op.id() != ID_address_of)
    return {};

  if(second_op.type() != pointer_type(pointer_type(empty_typet{})))
    return {};

  const exprt &object = to_address_of_expr(second_op).object();
  if(object.id() != ID_index)
    return {};

  const index_exprt &index_expr = to_index_expr(object);
  if(!index_expr.index().is_zero())
    return {};
  else
    return index_expr.array();
}

void goto_symext::symex_printf(
  statet &state,
  const exprt &rhs)
{
  PRECONDITION(!rhs.operands().empty());

  exprt tmp_rhs = rhs;
  clean_expr(tmp_rhs, state, false);
  tmp_rhs = state.rename(std::move(tmp_rhs), ns).get();
  do_simplify(tmp_rhs);

  const exprt::operandst &operands=tmp_rhs.operands();
  std::list<exprt> args;

  // we either have any number of operands or a va_list as second operand
  optionalt<exprt> va_args = get_va_args(operands);

  if(!va_args.has_value())
  {
    args.insert(args.end(), std::next(operands.begin()), operands.end());
  }
  else
  {
    clean_expr(*va_args, state, false);
    *va_args = state.field_sensitivity.apply(ns, state, *va_args, false);
    *va_args = state.rename(*va_args, ns).get();
    if(va_args->id() != ID_array)
    {
      // we were not able to constant-propagate va_args, and thus don't have
      // sufficient information to generate printf -- give up
      return;
    }

    for(const auto &op : va_args->operands())
    {
      exprt parameter = skip_typecast(op);
      if(parameter.id() == ID_address_of)
        parameter = to_address_of_expr(parameter).object();
      clean_expr(parameter, state, false);
      parameter = state.rename(std::move(parameter), ns).get();
      do_simplify(parameter);

      args.push_back(std::move(parameter));
    }
  }

  const irep_idt format_string=
    get_string_argument(operands[0], ns);

  if(!format_string.empty())
    target.output_fmt(
      state.guard.as_expr(),
      state.source, "printf", format_string, args);
}

void goto_symext::symex_input(
  statet &state,
  const codet &code)
{
  PRECONDITION(code.operands().size() >= 2);

  exprt id_arg = state.rename(code.op0(), ns).get();

  std::list<exprt> args;

  for(std::size_t i=1; i<code.operands().size(); i++)
  {
    exprt l2_arg = state.rename(code.operands()[i], ns).get();
    do_simplify(l2_arg);
    args.emplace_back(std::move(l2_arg));
  }

  const irep_idt input_id=get_string_argument(id_arg, ns);

  target.input(state.guard.as_expr(), state.source, input_id, args);
}

void goto_symext::symex_output(
  statet &state,
  const codet &code)
{
  PRECONDITION(code.operands().size() >= 2);
  exprt id_arg = state.rename(code.op0(), ns).get();

  std::list<renamedt<exprt, L2>> args;

  for(std::size_t i=1; i<code.operands().size(); i++)
  {
    renamedt<exprt, L2> l2_arg = state.rename(code.operands()[i], ns);
    if(symex_config.simplify_opt)
      l2_arg.simplify(ns);
    args.emplace_back(l2_arg);
  }

  const irep_idt output_id=get_string_argument(id_arg, ns);

  target.output(state.guard.as_expr(), state.source, output_id, args);
}

void goto_symext::symex_cpp_new(
  statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  bool do_array;

  PRECONDITION(code.type().id() == ID_pointer);

  const auto &pointer_type = to_pointer_type(code.type());

  do_array =
    (code.get(ID_statement) == ID_cpp_new_array ||
     code.get(ID_statement) == ID_java_new_array_data);

  dynamic_counter++;

  const std::string count_string(std::to_string(dynamic_counter));

  // value
  symbolt symbol;
  symbol.base_name=
    do_array?"dynamic_"+count_string+"_array":
             "dynamic_"+count_string+"_value";
  symbol.name = SYMEX_DYNAMIC_PREFIX + id2string(symbol.base_name);
  symbol.is_lvalue=true;
  if(code.get(ID_statement)==ID_cpp_new_array ||
     code.get(ID_statement)==ID_cpp_new)
    symbol.mode=ID_cpp;
  else if(code.get(ID_statement) == ID_java_new_array_data)
    symbol.mode=ID_java;
  else
    INVARIANT_WITH_IREP(false, "Unexpected side effect expression", code);

  if(do_array)
  {
    exprt size_arg =
      clean_expr(static_cast<const exprt &>(code.find(ID_size)), state, false);
    symbol.type = array_typet(pointer_type.subtype(), size_arg);
  }
  else
    symbol.type = pointer_type.subtype();

  symbol.type.set(ID_C_dynamic, true);

  state.symbol_table.add(symbol);

  // make symbol expression

  exprt rhs(ID_address_of, pointer_type);

  if(do_array)
  {
    rhs.add_to_operands(
      index_exprt(symbol.symbol_expr(), from_integer(0, index_type())));
  }
  else
    rhs.copy_to_operands(symbol.symbol_expr());

  symex_assign(state, lhs, rhs);
}

void goto_symext::symex_cpp_delete(
  statet &,
  const codet &)
{
  // TODO
  #if 0
  bool do_array=code.get(ID_statement)==ID_cpp_delete_array;
  #endif
}

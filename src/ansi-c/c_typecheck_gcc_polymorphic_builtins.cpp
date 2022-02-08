/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Type Checking

#include "c_typecheck_base.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/pointer_expr.h>
#include <util/std_types.h>
#include <util/string_constant.h>

#include <goto-programs/goto_instruction_code.h>

#include <atomic>

#include "c_expr.h"

static symbol_exprt typecheck_sync_with_pointer_parameter(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  messaget log(message_handler);

  // adjust return type of function to match pointer subtype
  if(arguments.size() < 2)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " expects at least two arguments"
                << messaget::eom;
    throw 0;
  }

  const exprt &ptr_arg = arguments.front();

  if(ptr_arg.type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as first argument"
                << messaget::eom;
    throw 0;
  }

  const auto &pointer_type = to_pointer_type(ptr_arg.type());

  code_typet t{{code_typet::parametert(ptr_arg.type()),
                code_typet::parametert(pointer_type.base_type())},
               pointer_type.base_type()};
  t.make_ellipsis();
  symbol_exprt result{identifier, std::move(t)};
  result.add_source_location() = source_location;

  return result;
}

static symbol_exprt typecheck_sync_compare_swap(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  messaget log(message_handler);

  // adjust return type of function to match pointer subtype
  if(arguments.size() < 3)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " expects at least three arguments"
                << messaget::eom;
    throw 0;
  }

  const exprt &ptr_arg = arguments.front();

  if(ptr_arg.type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as first argument"
                << messaget::eom;
    throw 0;
  }

  const typet &base_type = to_pointer_type(ptr_arg.type()).base_type();
  typet sync_return_type = base_type;
  if(identifier == ID___sync_bool_compare_and_swap)
    sync_return_type = c_bool_type();

  code_typet t{{code_typet::parametert(ptr_arg.type()),
                code_typet::parametert(base_type),
                code_typet::parametert(base_type)},
               sync_return_type};
  t.make_ellipsis();
  symbol_exprt result{identifier, std::move(t)};
  result.add_source_location() = source_location;

  return result;
}

static symbol_exprt typecheck_sync_lock_release(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  messaget log(message_handler);

  // adjust return type of function to match pointer subtype
  if(arguments.empty())
  {
    log.error().source_location = source_location;
    log.error() << identifier << " expects at least one argument"
                << messaget::eom;
    throw 0;
  }

  const exprt &ptr_arg = arguments.front();

  if(ptr_arg.type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as first argument"
                << messaget::eom;
    throw 0;
  }

  code_typet t{{code_typet::parametert(ptr_arg.type())}, void_type()};
  t.make_ellipsis();
  symbol_exprt result{identifier, std::move(t)};
  result.add_source_location() = source_location;

  return result;
}

static symbol_exprt typecheck_atomic_load_n(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  // type __atomic_load_n(type *ptr, int memorder)
  messaget log(message_handler);

  if(arguments.size() != 2)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " expects two arguments" << messaget::eom;
    throw 0;
  }

  const exprt &ptr_arg = arguments.front();

  if(ptr_arg.type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as first argument"
                << messaget::eom;
    throw 0;
  }

  const code_typet t(
    {code_typet::parametert(ptr_arg.type()),
     code_typet::parametert(signed_int_type())},
    to_pointer_type(ptr_arg.type()).base_type());
  symbol_exprt result(identifier, t);
  result.add_source_location() = source_location;
  return result;
}

static symbol_exprt typecheck_atomic_store_n(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  // void __atomic_store_n(type *ptr, type val, int memorder)
  messaget log(message_handler);

  if(arguments.size() != 3)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " expects three arguments" << messaget::eom;
    throw 0;
  }

  const exprt &ptr_arg = arguments.front();

  if(ptr_arg.type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as first argument"
                << messaget::eom;
    throw 0;
  }

  const auto &base_type = to_pointer_type(ptr_arg.type()).base_type();

  const code_typet t(
    {code_typet::parametert(ptr_arg.type()),
     code_typet::parametert(base_type),
     code_typet::parametert(signed_int_type())},
    void_type());
  symbol_exprt result(identifier, t);
  result.add_source_location() = source_location;
  return result;
}

static symbol_exprt typecheck_atomic_exchange_n(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  // type __atomic_exchange_n(type *ptr, type val, int memorder)
  messaget log(message_handler);

  if(arguments.size() != 3)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " expects three arguments" << messaget::eom;
    throw 0;
  }

  const exprt &ptr_arg = arguments.front();

  if(ptr_arg.type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as first argument"
                << messaget::eom;
    throw 0;
  }

  const auto &base_type = to_pointer_type(ptr_arg.type()).base_type();

  const code_typet t(
    {code_typet::parametert(ptr_arg.type()),
     code_typet::parametert(base_type),
     code_typet::parametert(signed_int_type())},
    base_type);
  symbol_exprt result(identifier, t);
  result.add_source_location() = source_location;
  return result;
}

static symbol_exprt typecheck_atomic_load_store(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  // void __atomic_load(type *ptr, type *ret, int memorder)
  // void __atomic_store(type *ptr, type *val, int memorder)
  messaget log(message_handler);

  if(arguments.size() != 3)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " expects three arguments" << messaget::eom;
    throw 0;
  }

  if(arguments[0].type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as first argument"
                << messaget::eom;
    throw 0;
  }

  if(arguments[1].type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as second argument"
                << messaget::eom;
    throw 0;
  }

  const exprt &ptr_arg = arguments.front();

  const code_typet t(
    {code_typet::parametert(ptr_arg.type()),
     code_typet::parametert(ptr_arg.type()),
     code_typet::parametert(signed_int_type())},
    void_type());
  symbol_exprt result(identifier, t);
  result.add_source_location() = source_location;
  return result;
}

static symbol_exprt typecheck_atomic_exchange(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  // void __atomic_exchange(type *ptr, type *val, type *ret, int memorder)
  messaget log(message_handler);

  if(arguments.size() != 4)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " expects four arguments" << messaget::eom;
    throw 0;
  }

  if(arguments[0].type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as first argument"
                << messaget::eom;
    throw 0;
  }

  if(arguments[1].type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as second argument"
                << messaget::eom;
    throw 0;
  }

  if(arguments[2].type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as third argument"
                << messaget::eom;
    throw 0;
  }

  const exprt &ptr_arg = arguments.front();

  const code_typet t(
    {code_typet::parametert(ptr_arg.type()),
     code_typet::parametert(ptr_arg.type()),
     code_typet::parametert(ptr_arg.type()),
     code_typet::parametert(signed_int_type())},
    void_type());
  symbol_exprt result(identifier, t);
  result.add_source_location() = source_location;
  return result;
}

static symbol_exprt typecheck_atomic_compare_exchange(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  // bool __atomic_compare_exchange_n(type *ptr, type *expected, type
  // desired, bool weak, int success_memorder, int failure_memorder)
  // bool __atomic_compare_exchange(type *ptr, type *expected, type
  // *desired, bool weak, int success_memorder, int failure_memorder)
  messaget log(message_handler);

  if(arguments.size() != 6)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " expects six arguments" << messaget::eom;
    throw 0;
  }

  if(arguments[0].type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as first argument"
                << messaget::eom;
    throw 0;
  }

  if(arguments[1].type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as second argument"
                << messaget::eom;
    throw 0;
  }

  if(
    identifier == ID___atomic_compare_exchange &&
    arguments[2].type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error() << identifier << " takes a pointer as third argument"
                << messaget::eom;
    throw 0;
  }

  const exprt &ptr_arg = arguments.front();

  code_typet::parameterst parameters;
  parameters.push_back(code_typet::parametert(ptr_arg.type()));
  parameters.push_back(code_typet::parametert(ptr_arg.type()));

  if(identifier == ID___atomic_compare_exchange)
    parameters.push_back(code_typet::parametert(ptr_arg.type()));
  else
    parameters.push_back(
      code_typet::parametert(to_pointer_type(ptr_arg.type()).base_type()));

  parameters.push_back(code_typet::parametert(c_bool_type()));
  parameters.push_back(code_typet::parametert(signed_int_type()));
  parameters.push_back(code_typet::parametert(signed_int_type()));
  code_typet t(std::move(parameters), c_bool_type());
  symbol_exprt result(identifier, t);
  result.add_source_location() = source_location;
  return result;
}

static symbol_exprt typecheck_atomic_op_fetch(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  messaget log(message_handler);

  if(arguments.size() != 3)
  {
    log.error().source_location = source_location;
    log.error() << "__atomic_*_fetch primitives take three arguments"
                << messaget::eom;
    throw 0;
  }

  const exprt &ptr_arg = arguments.front();

  if(ptr_arg.type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error()
      << "__atomic_*_fetch primitives take a pointer as first argument"
      << messaget::eom;
    throw 0;
  }

  code_typet t(
    {code_typet::parametert(ptr_arg.type()),
     code_typet::parametert(to_pointer_type(ptr_arg.type()).base_type()),
     code_typet::parametert(signed_int_type())},
    to_pointer_type(ptr_arg.type()).base_type());
  symbol_exprt result(identifier, std::move(t));
  result.add_source_location() = source_location;
  return result;
}

static symbol_exprt typecheck_atomic_fetch_op(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  messaget log(message_handler);

  if(arguments.size() != 3)
  {
    log.error().source_location = source_location;
    log.error() << "__atomic_fetch_* primitives take three arguments"
                << messaget::eom;
    throw 0;
  }

  const exprt &ptr_arg = arguments.front();

  if(ptr_arg.type().id() != ID_pointer)
  {
    log.error().source_location = source_location;
    log.error()
      << "__atomic_fetch_* primitives take a pointer as first argument"
      << messaget::eom;
    throw 0;
  }

  code_typet t(
    {code_typet::parametert(ptr_arg.type()),
     code_typet::parametert(to_pointer_type(ptr_arg.type()).base_type()),
     code_typet::parametert(signed_int_type())},
    to_pointer_type(ptr_arg.type()).base_type());
  symbol_exprt result(identifier, std::move(t));
  result.add_source_location() = source_location;
  return result;
}

optionalt<symbol_exprt> c_typecheck_baset::typecheck_gcc_polymorphic_builtin(
  const irep_idt &identifier,
  const exprt::operandst &arguments,
  const source_locationt &source_location)
{
  // the arguments need not be type checked just yet, thus do not make
  // assumptions that would require type checking

  if(
    identifier == ID___sync_fetch_and_add ||
    identifier == ID___sync_fetch_and_sub ||
    identifier == ID___sync_fetch_and_or ||
    identifier == ID___sync_fetch_and_and ||
    identifier == ID___sync_fetch_and_xor ||
    identifier == ID___sync_fetch_and_nand ||
    identifier == ID___sync_add_and_fetch ||
    identifier == ID___sync_sub_and_fetch ||
    identifier == ID___sync_or_and_fetch ||
    identifier == ID___sync_and_and_fetch ||
    identifier == ID___sync_xor_and_fetch ||
    identifier == ID___sync_nand_and_fetch ||
    identifier == ID___sync_lock_test_and_set)
  {
    // These are polymorphic, see
    // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fsync-Builtins.html
    return typecheck_sync_with_pointer_parameter(
      identifier, arguments, source_location, get_message_handler());
  }
  else if(
    identifier == ID___sync_bool_compare_and_swap ||
    identifier == ID___sync_val_compare_and_swap)
  {
    // These are polymorphic, see
    // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fsync-Builtins.html
    return typecheck_sync_compare_swap(
      identifier, arguments, source_location, get_message_handler());
  }
  else if(identifier == ID___sync_lock_release)
  {
    // This is polymorphic, see
    // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fsync-Builtins.html
    return typecheck_sync_lock_release(
      identifier, arguments, source_location, get_message_handler());
  }
  else if(identifier == ID___atomic_load_n)
  {
    // These are polymorphic
    // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
    return typecheck_atomic_load_n(
      identifier, arguments, source_location, get_message_handler());
  }
  else if(identifier == ID___atomic_store_n)
  {
    // These are polymorphic
    // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
    return typecheck_atomic_store_n(
      identifier, arguments, source_location, get_message_handler());
  }
  else if(identifier == ID___atomic_exchange_n)
  {
    // These are polymorphic
    // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
    return typecheck_atomic_exchange_n(
      identifier, arguments, source_location, get_message_handler());
  }
  else if(identifier == ID___atomic_load || identifier == ID___atomic_store)
  {
    // These are polymorphic
    // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
    return typecheck_atomic_load_store(
      identifier, arguments, source_location, get_message_handler());
  }
  else if(identifier == ID___atomic_exchange)
  {
    // These are polymorphic
    // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
    return typecheck_atomic_exchange(
      identifier, arguments, source_location, get_message_handler());
  }
  else if(
    identifier == ID___atomic_compare_exchange_n ||
    identifier == ID___atomic_compare_exchange)
  {
    // These are polymorphic
    // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
    return typecheck_atomic_compare_exchange(
      identifier, arguments, source_location, get_message_handler());
  }
  else if(
    identifier == ID___atomic_add_fetch ||
    identifier == ID___atomic_sub_fetch ||
    identifier == ID___atomic_and_fetch ||
    identifier == ID___atomic_xor_fetch || identifier == ID___atomic_or_fetch ||
    identifier == ID___atomic_nand_fetch)
  {
    // These are polymorphic
    // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
    return typecheck_atomic_op_fetch(
      identifier, arguments, source_location, get_message_handler());
  }
  else if(
    identifier == ID___atomic_fetch_add ||
    identifier == ID___atomic_fetch_sub ||
    identifier == ID___atomic_fetch_and ||
    identifier == ID___atomic_fetch_xor || identifier == ID___atomic_fetch_or ||
    identifier == ID___atomic_fetch_nand)
  {
    // These are polymorphic
    // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
    return typecheck_atomic_fetch_op(
      identifier, arguments, source_location, get_message_handler());
  }

  return {};
}

static symbolt result_symbol(
  const irep_idt &identifier,
  const typet &type,
  const source_locationt &source_location,
  symbol_tablet &symbol_table)
{
  symbolt symbol;
  symbol.name = id2string(identifier) + "::1::result";
  symbol.base_name = "result";
  symbol.type = type;
  symbol.mode = ID_C;
  symbol.location = source_location;
  symbol.is_file_local = true;
  symbol.is_lvalue = true;
  symbol.is_thread_local = true;

  symbol_table.add(symbol);

  return symbol;
}

static void instantiate_atomic_fetch_op(
  const irep_idt &identifier,
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  symbol_tablet &symbol_table,
  code_blockt &block)
{
  // type __sync_fetch_and_OP(type *ptr, type value, ...)
  // { type result; result = *ptr; *ptr = result OP value; return result; }
  const typet &type = code_type.return_type();

  const symbol_exprt result =
    result_symbol(identifier_with_type, type, source_location, symbol_table)
      .symbol_expr();
  block.add(codet{ID_decl_block, {code_frontend_declt{result}}});

  // place operations on *ptr in an atomic section
  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_begin"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  // build *ptr
  const dereference_exprt deref_ptr{parameter_exprs[0]};

  block.add(code_frontend_assignt{result, deref_ptr});

  // build *ptr = result OP arguments[1];
  irep_idt op_id = identifier == ID___atomic_fetch_add
                     ? ID_plus
                     : identifier == ID___atomic_fetch_sub
                         ? ID_minus
                         : identifier == ID___atomic_fetch_or
                             ? ID_bitor
                             : identifier == ID___atomic_fetch_and
                                 ? ID_bitand
                                 : identifier == ID___atomic_fetch_xor
                                     ? ID_bitxor
                                     : identifier == ID___atomic_fetch_nand
                                         ? ID_bitnand
                                         : ID_nil;
  binary_exprt op_expr{result, op_id, parameter_exprs[1], type};
  block.add(code_frontend_assignt{deref_ptr, std::move(op_expr)});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless("__atomic_thread_fence"),
    {parameter_exprs[2]},
    typet{},
    source_location}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_end"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  block.add(code_returnt{result});
}

static void instantiate_atomic_op_fetch(
  const irep_idt &identifier,
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  symbol_tablet &symbol_table,
  code_blockt &block)
{
  // type __sync_OP_and_fetch(type *ptr, type value, ...)
  // { type result; result = *ptr OP value; *ptr = result; return result; }
  const typet &type = code_type.return_type();

  const symbol_exprt result =
    result_symbol(identifier_with_type, type, source_location, symbol_table)
      .symbol_expr();
  block.add(codet{ID_decl_block, {code_frontend_declt{result}}});

  // place operations on *ptr in an atomic section
  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_begin"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  // build *ptr
  const dereference_exprt deref_ptr{parameter_exprs[0]};

  // build result = *ptr OP arguments[1];
  irep_idt op_id = identifier == ID___atomic_add_fetch
                     ? ID_plus
                     : identifier == ID___atomic_sub_fetch
                         ? ID_minus
                         : identifier == ID___atomic_or_fetch
                             ? ID_bitor
                             : identifier == ID___atomic_and_fetch
                                 ? ID_bitand
                                 : identifier == ID___atomic_xor_fetch
                                     ? ID_bitxor
                                     : identifier == ID___atomic_nand_fetch
                                         ? ID_bitnand
                                         : ID_nil;
  binary_exprt op_expr{deref_ptr, op_id, parameter_exprs[1], type};
  block.add(code_frontend_assignt{result, std::move(op_expr)});

  block.add(code_frontend_assignt{deref_ptr, result});

  // this instruction implies an mfence, i.e., WRfence
  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless("__atomic_thread_fence"),
    {parameter_exprs[2]},
    typet{},
    source_location}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_end"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  block.add(code_returnt{result});
}

static void instantiate_sync_fetch(
  const irep_idt &identifier,
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  code_blockt &block)
{
  // implement by calling their __atomic_ counterparts with memorder SEQ_CST
  std::string atomic_name = "__atomic_" + id2string(identifier).substr(7);
  atomic_name.replace(atomic_name.find("_and_"), 5, "_");

  exprt::operandst arguments{
    parameter_exprs[0],
    parameter_exprs[1],
    from_integer(std::memory_order_seq_cst, signed_int_type())};

  block.add(code_returnt{
    side_effect_expr_function_callt{symbol_exprt::typeless(atomic_name),
                                    std::move(arguments),
                                    typet{},
                                    source_location}});
}

static void instantiate_sync_bool_compare_and_swap(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  code_blockt &block)
{
  // These builtins perform an atomic compare and swap. That is, if the
  // current value of *ptr is oldval, then write newval into *ptr.  The
  // "bool" version returns true if the comparison is successful and
  // newval was written.  The "val" version returns the contents of *ptr
  // before the operation.

  // _Bool __sync_bool_compare_and_swap(type *ptr, type old, type new, ...)

  block.add(code_returnt{side_effect_expr_function_callt{
    symbol_exprt::typeless(ID___atomic_compare_exchange),
    {parameter_exprs[0],
     address_of_exprt{parameter_exprs[1]},
     address_of_exprt{parameter_exprs[2]},
     from_integer(0, c_bool_type()),
     from_integer(std::memory_order_seq_cst, signed_int_type()),
     from_integer(std::memory_order_seq_cst, signed_int_type())},
    typet{},
    source_location}});
}

static void instantiate_sync_val_compare_and_swap(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  symbol_tablet &symbol_table,
  code_blockt &block)
{
  // type __sync_val_compare_and_swap(type *ptr, type old, type new, ...)
  // { type result = *ptr; if(result == old) *ptr = new; return result; }
  const typet &type = code_type.return_type();

  const symbol_exprt result =
    result_symbol(identifier_with_type, type, source_location, symbol_table)
      .symbol_expr();
  block.add(codet{ID_decl_block, {code_frontend_declt{result}}});

  // place operations on *ptr in an atomic section
  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_begin"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  // build *ptr
  const dereference_exprt deref_ptr{parameter_exprs[0]};

  block.add(code_frontend_assignt{result, deref_ptr});

  code_frontend_assignt assign{deref_ptr, parameter_exprs[2]};
  assign.add_source_location() = source_location;
  block.add(code_ifthenelset{equal_exprt{result, parameter_exprs[1]},
                             std::move(assign)});

  // this instruction implies an mfence, i.e., WRfence
  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "fence"),
    {string_constantt{ID_WRfence}},
    typet{},
    source_location}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_end"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  block.add(code_returnt{result});
}

static void instantiate_sync_lock_test_and_set(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  symbol_tablet &symbol_table,
  code_blockt &block)
{
  // type __sync_lock_test_and_set (type *ptr, type value, ...)

  // This builtin, as described by Intel, is not a traditional
  // test-and-set operation, but rather an atomic exchange operation.
  // It writes value into *ptr, and returns the previous contents of
  // *ptr.  Many targets have only minimal support for such locks, and
  // do not support a full exchange operation.  In this case, a target
  // may support reduced functionality here by which the only valid
  // value to store is the immediate constant 1.  The exact value
  // actually stored in *ptr is implementation defined.
  const typet &type = code_type.return_type();

  const symbol_exprt result =
    result_symbol(identifier_with_type, type, source_location, symbol_table)
      .symbol_expr();
  block.add(codet{ID_decl_block, {code_frontend_declt{result}}});

  // place operations on *ptr in an atomic section
  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_begin"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  // build *ptr
  const dereference_exprt deref_ptr{parameter_exprs[0]};

  block.add(code_frontend_assignt{result, deref_ptr});

  block.add(code_frontend_assignt{deref_ptr, parameter_exprs[1]});

  // This built-in function is not a full barrier, but rather an acquire
  // barrier.
  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "fence"),
    {string_constantt{ID_RRfence}, {string_constantt{ID_RRfence}}},
    typet{},
    source_location}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_end"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  block.add(code_returnt{result});
}

static void instantiate_sync_lock_release(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  code_blockt &block)
{
  // void __sync_lock_release (type *ptr, ...)

  // This built-in function releases the lock acquired by
  // __sync_lock_test_and_set. Normally this means writing the constant 0 to
  // *ptr.
  const typet &type = to_pointer_type(parameter_exprs[0].type()).base_type();

  // place operations on *ptr in an atomic section
  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_begin"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  block.add(code_frontend_assignt{dereference_exprt{parameter_exprs[0]},
                                  typecast_exprt::conditional_cast(
                                    from_integer(0, signed_int_type()), type)});

  // This built-in function is not a full barrier, but rather a release
  // barrier.
  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "fence"),
    {string_constantt{ID_WRfence}, {string_constantt{ID_WWfence}}},
    typet{},
    source_location}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_end"),
    {},
    code_typet{{}, void_type()},
    source_location}});
}

static void instantiate_atomic_load(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  code_blockt &block)
{
  // void __atomic_load (type *ptr, type *ret, int memorder)
  // This is the generic version of an atomic load. It returns the contents of
  // *ptr in *ret.

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_begin"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  block.add(code_frontend_assignt{dereference_exprt{parameter_exprs[1]},
                                  dereference_exprt{parameter_exprs[0]}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless("__atomic_thread_fence"),
    {parameter_exprs[2]},
    typet{},
    source_location}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_end"),
    {},
    code_typet{{}, void_type()},
    source_location}});
}

static void instantiate_atomic_load_n(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  symbol_tablet &symbol_table,
  code_blockt &block)
{
  // type __atomic_load_n (type *ptr, int memorder)
  // This built-in function implements an atomic load operation. It returns
  // the contents of *ptr.
  const typet &type = code_type.return_type();

  const symbol_exprt result =
    result_symbol(identifier_with_type, type, source_location, symbol_table)
      .symbol_expr();
  block.add(codet{ID_decl_block, {code_frontend_declt{result}}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(ID___atomic_load),
    {parameter_exprs[0], address_of_exprt{result}, parameter_exprs[1]},
    typet{},
    source_location}});

  block.add(code_returnt{result});
}

static void instantiate_atomic_store(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  code_blockt &block)
{
  //  void __atomic_store (type *ptr, type *val, int memorder)
  //  This is the generic version of an atomic store. It stores the value of
  //  *val into *ptr.

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_begin"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  block.add(code_frontend_assignt{dereference_exprt{parameter_exprs[0]},
                                  dereference_exprt{parameter_exprs[1]}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless("__atomic_thread_fence"),
    {parameter_exprs[2]},
    typet{},
    source_location}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_end"),
    {},
    code_typet{{}, void_type()},
    source_location}});
}

static void instantiate_atomic_store_n(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  code_blockt &block)
{
  // void __atomic_store_n (type *ptr, type val, int memorder)
  // This built-in function implements an atomic store operation. It writes
  // val into *ptr.

  block.add(code_expressiont{
    side_effect_expr_function_callt{symbol_exprt::typeless(ID___atomic_store),
                                    {parameter_exprs[0],
                                     address_of_exprt{parameter_exprs[1]},
                                     parameter_exprs[2]},
                                    typet{},
                                    source_location}});
}

static void instantiate_atomic_exchange(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  code_blockt &block)
{
  // void __atomic_exchange (type *ptr, type *val, type *ret, int memorder)
  // This is the generic version of an atomic exchange. It stores the contents
  // of *val into *ptr. The original value of *ptr is copied into *ret.

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_begin"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  block.add(code_frontend_assignt{dereference_exprt{parameter_exprs[2]},
                                  dereference_exprt{parameter_exprs[0]}});
  block.add(code_frontend_assignt{dereference_exprt{parameter_exprs[0]},
                                  dereference_exprt{parameter_exprs[1]}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless("__atomic_thread_fence"),
    {parameter_exprs[3]},
    typet{},
    source_location}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_end"),
    {},
    code_typet{{}, void_type()},
    source_location}});
}

static void instantiate_atomic_exchange_n(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  symbol_tablet &symbol_table,
  code_blockt &block)
{
  // type __atomic_exchange_n (type *ptr, type val, int memorder)
  // This built-in function implements an atomic exchange operation. It writes
  // val into *ptr, and returns the previous contents of *ptr.
  const typet &type = code_type.return_type();

  const symbol_exprt result =
    result_symbol(identifier_with_type, type, source_location, symbol_table)
      .symbol_expr();
  block.add(codet{ID_decl_block, {code_frontend_declt{result}}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(ID___atomic_exchange),
    {parameter_exprs[0],
     address_of_exprt{parameter_exprs[1]},
     address_of_exprt{result},
     parameter_exprs[2]},
    typet{},
    source_location}});

  block.add(code_returnt{result});
}

static void instantiate_atomic_compare_exchange(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  symbol_tablet &symbol_table,
  code_blockt &block)
{
  // bool __atomic_compare_exchange (type *ptr, type *expected, type *desired,
  // bool weak, int success_memorder, int failure_memorder)
  // This built-in function implements an atomic compare and exchange
  // operation. This compares the contents of *ptr with the contents of
  // *expected. If equal, the operation is a read-modify-write operation that
  // writes *desired into *ptr. If they are not equal, the operation is a read
  // and the current contents of *ptr are written into *expected. weak is true
  // for weak compare_exchange, which may fail spuriously, and false for the
  // strong variation, which never fails spuriously. Many targets only offer
  // the strong variation and ignore the parameter.

  const symbol_exprt result =
    result_symbol(
      identifier_with_type, c_bool_type(), source_location, symbol_table)
      .symbol_expr();
  block.add(codet{ID_decl_block, {code_frontend_declt{result}}});

  // place operations on *ptr in an atomic section
  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_begin"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  // build *ptr
  const dereference_exprt deref_ptr{parameter_exprs[0]};

  block.add(code_frontend_assignt{
    result,
    typecast_exprt::conditional_cast(
      equal_exprt{deref_ptr, dereference_exprt{parameter_exprs[1]}},
      result.type())});

  // we never fail spuriously, and ignore parameter_exprs[3]
  code_frontend_assignt assign{deref_ptr,
                               dereference_exprt{parameter_exprs[2]}};
  assign.add_source_location() = source_location;
  code_expressiont success_fence{side_effect_expr_function_callt{
    symbol_exprt::typeless("__atomic_thread_fence"),
    {parameter_exprs[4]},
    typet{},
    source_location}};
  success_fence.add_source_location() = source_location;

  code_frontend_assignt assign_not_equal{dereference_exprt{parameter_exprs[1]},
                                         deref_ptr};
  assign_not_equal.add_source_location() = source_location;
  code_expressiont failure_fence{side_effect_expr_function_callt{
    symbol_exprt::typeless("__atomic_thread_fence"),
    {parameter_exprs[5]},
    typet{},
    source_location}};
  failure_fence.add_source_location() = source_location;

  block.add(code_ifthenelset{
    result,
    code_blockt{{std::move(assign), std::move(success_fence)}},
    code_blockt{{std::move(assign_not_equal), std::move(failure_fence)}}});

  block.add(code_expressiont{side_effect_expr_function_callt{
    symbol_exprt::typeless(CPROVER_PREFIX "atomic_end"),
    {},
    code_typet{{}, void_type()},
    source_location}});

  block.add(code_returnt{result});
}

static void instantiate_atomic_compare_exchange_n(
  const irep_idt &identifier_with_type,
  const code_typet &code_type,
  const source_locationt &source_location,
  const std::vector<symbol_exprt> &parameter_exprs,
  code_blockt &block)
{
  // bool __atomic_compare_exchange_n (type *ptr, type *expected, type
  // desired, bool weak, int success_memorder, int failure_memorder)

  block.add(code_returnt{side_effect_expr_function_callt{
    symbol_exprt::typeless(ID___atomic_compare_exchange),
    {parameter_exprs[0],
     parameter_exprs[1],
     address_of_exprt{parameter_exprs[2]},
     parameter_exprs[3],
     parameter_exprs[4],
     parameter_exprs[5]},
    typet{},
    source_location}});
}

code_blockt c_typecheck_baset::instantiate_gcc_polymorphic_builtin(
  const irep_idt &identifier,
  const symbol_exprt &function_symbol)
{
  const irep_idt &identifier_with_type = function_symbol.get_identifier();
  const code_typet &code_type = to_code_type(function_symbol.type());
  const source_locationt &source_location = function_symbol.source_location();

  std::vector<symbol_exprt> parameter_exprs;
  parameter_exprs.reserve(code_type.parameters().size());
  for(const auto &parameter : code_type.parameters())
  {
    parameter_exprs.push_back(lookup(parameter.get_identifier()).symbol_expr());
  }

  code_blockt block;

  if(
    identifier == ID___atomic_fetch_add ||
    identifier == ID___atomic_fetch_sub || identifier == ID___atomic_fetch_or ||
    identifier == ID___atomic_fetch_and ||
    identifier == ID___atomic_fetch_xor || identifier == ID___atomic_fetch_nand)
  {
    instantiate_atomic_fetch_op(
      identifier,
      identifier_with_type,
      code_type,
      source_location,
      parameter_exprs,
      symbol_table,
      block);
  }
  else if(
    identifier == ID___atomic_add_fetch ||
    identifier == ID___atomic_sub_fetch || identifier == ID___atomic_or_fetch ||
    identifier == ID___atomic_and_fetch ||
    identifier == ID___atomic_xor_fetch || identifier == ID___atomic_nand_fetch)
  {
    instantiate_atomic_op_fetch(
      identifier,
      identifier_with_type,
      code_type,
      source_location,
      parameter_exprs,
      symbol_table,
      block);
  }
  else if(
    identifier == ID___sync_fetch_and_add ||
    identifier == ID___sync_fetch_and_sub ||
    identifier == ID___sync_fetch_and_or ||
    identifier == ID___sync_fetch_and_and ||
    identifier == ID___sync_fetch_and_xor ||
    identifier == ID___sync_fetch_and_nand ||
    identifier == ID___sync_add_and_fetch ||
    identifier == ID___sync_sub_and_fetch ||
    identifier == ID___sync_or_and_fetch ||
    identifier == ID___sync_and_and_fetch ||
    identifier == ID___sync_xor_and_fetch ||
    identifier == ID___sync_nand_and_fetch)
  {
    instantiate_sync_fetch(
      identifier,
      identifier_with_type,
      code_type,
      source_location,
      parameter_exprs,
      block);
  }
  else if(identifier == ID___sync_bool_compare_and_swap)
  {
    instantiate_sync_bool_compare_and_swap(
      identifier_with_type, code_type, source_location, parameter_exprs, block);
  }
  else if(identifier == ID___sync_val_compare_and_swap)
  {
    instantiate_sync_val_compare_and_swap(
      identifier_with_type,
      code_type,
      source_location,
      parameter_exprs,
      symbol_table,
      block);
  }
  else if(identifier == ID___sync_lock_test_and_set)
  {
    instantiate_sync_lock_test_and_set(
      identifier_with_type,
      code_type,
      source_location,
      parameter_exprs,
      symbol_table,
      block);
  }
  else if(identifier == ID___sync_lock_release)
  {
    instantiate_sync_lock_release(
      identifier_with_type, code_type, source_location, parameter_exprs, block);
  }
  else if(identifier == ID___atomic_load)
  {
    instantiate_atomic_load(
      identifier_with_type, code_type, source_location, parameter_exprs, block);
  }
  else if(identifier == ID___atomic_load_n)
  {
    instantiate_atomic_load_n(
      identifier_with_type,
      code_type,
      source_location,
      parameter_exprs,
      symbol_table,
      block);
  }
  else if(identifier == ID___atomic_store)
  {
    instantiate_atomic_store(
      identifier_with_type, code_type, source_location, parameter_exprs, block);
  }
  else if(identifier == ID___atomic_store_n)
  {
    instantiate_atomic_store_n(
      identifier_with_type, code_type, source_location, parameter_exprs, block);
  }
  else if(identifier == ID___atomic_exchange)
  {
    instantiate_atomic_exchange(
      identifier_with_type, code_type, source_location, parameter_exprs, block);
  }
  else if(identifier == ID___atomic_exchange_n)
  {
    instantiate_atomic_exchange_n(
      identifier_with_type,
      code_type,
      source_location,
      parameter_exprs,
      symbol_table,
      block);
  }
  else if(identifier == ID___atomic_compare_exchange)
  {
    instantiate_atomic_compare_exchange(
      identifier_with_type,
      code_type,
      source_location,
      parameter_exprs,
      symbol_table,
      block);
  }
  else if(identifier == ID___atomic_compare_exchange_n)
  {
    instantiate_atomic_compare_exchange_n(
      identifier_with_type, code_type, source_location, parameter_exprs, block);
  }
  else
  {
    UNREACHABLE;
  }

  for(auto &statement : block.statements())
    statement.add_source_location() = source_location;

  return block;
}

exprt c_typecheck_baset::typecheck_shuffle_vector(
  const side_effect_expr_function_callt &expr)
{
  const exprt &f_op = expr.function();
  const source_locationt &source_location = expr.source_location();
  const irep_idt &identifier = to_symbol_expr(f_op).get_identifier();

  exprt::operandst arguments = expr.arguments();

  if(identifier == "__builtin_shuffle")
  {
    // https://gcc.gnu.org/onlinedocs/gcc/Vector-Extensions.html and
    // https://github.com/OpenCL/man/blob/master/shuffle.adoc
    if(arguments.size() != 2 && arguments.size() != 3)
    {
      error().source_location = f_op.source_location();
      error() << "__builtin_shuffle expects two or three arguments" << eom;
      throw 0;
    }

    for(exprt &arg : arguments)
    {
      if(arg.type().id() != ID_vector)
      {
        error().source_location = f_op.source_location();
        error() << "__builtin_shuffle expects vector arguments" << eom;
        throw 0;
      }
    }

    const exprt &arg0 = arguments[0];
    const vector_typet &input_vec_type = to_vector_type(arg0.type());

    optionalt<exprt> arg1;
    if(arguments.size() == 3)
    {
      if(arguments[1].type() != input_vec_type)
      {
        error().source_location = f_op.source_location();
        error() << "__builtin_shuffle expects input vectors of the same type"
                << eom;
        throw 0;
      }
      arg1 = arguments[1];
    }
    const exprt &indices = arguments.back();
    const vector_typet &indices_type = to_vector_type(indices.type());
    const std::size_t indices_size =
      numeric_cast_v<std::size_t>(indices_type.size());

    exprt::operandst operands;
    operands.reserve(indices_size);

    auto input_size = numeric_cast<mp_integer>(input_vec_type.size());
    CHECK_RETURN(input_size.has_value());
    if(arg1.has_value())
      input_size = *input_size * 2;
    constant_exprt size =
      from_integer(*input_size, indices_type.element_type());

    for(std::size_t i = 0; i < indices_size; ++i)
    {
      // only the least significant bits of each mask element are considered
      mod_exprt mod_index{index_exprt{indices, from_integer(i, c_index_type())},
                          size};
      mod_index.add_source_location() = source_location;
      operands.push_back(std::move(mod_index));
    }

    return shuffle_vector_exprt{arg0, arg1, std::move(operands)};
  }
  else if(identifier == "__builtin_shufflevector")
  {
    // https://clang.llvm.org/docs/LanguageExtensions.html#langext-builtin-shufflevector
    if(arguments.size() < 2)
    {
      error().source_location = f_op.source_location();
      error() << "__builtin_shufflevector expects two or more arguments" << eom;
      throw 0;
    }

    exprt::operandst operands;
    operands.reserve(arguments.size() - 2);

    for(std::size_t i = 0; i < arguments.size(); ++i)
    {
      exprt &arg_i = arguments[i];

      if(i <= 1 && arg_i.type().id() != ID_vector)
      {
        error().source_location = f_op.source_location();
        error() << "__builtin_shufflevector expects two vectors as argument"
                << eom;
        throw 0;
      }
      else if(i > 1)
      {
        if(!is_signed_or_unsigned_bitvector(arg_i.type()))
        {
          error().source_location = f_op.source_location();
          error() << "__builtin_shufflevector expects integer index" << eom;
          throw 0;
        }

        make_constant(arg_i);

        const auto int_index = numeric_cast<mp_integer>(arg_i);
        CHECK_RETURN(int_index.has_value());

        if(*int_index == -1)
        {
          operands.push_back(from_integer(0, arg_i.type()));
          operands.back().add_source_location() = source_location;
        }
        else
          operands.push_back(arg_i);
      }
    }

    return shuffle_vector_exprt{
      arguments[0], arguments[1], std::move(operands)};
  }
  else
    UNREACHABLE;
}

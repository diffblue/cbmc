// Copyrigth 2018 Author: Malte Mues <mail.mues@gmail.com>
#ifdef __linux__

#include "analyze_symbol.h"
#include "gdb_api.h"

#include <algorithm>
#include <regex>

#include <goto-programs/goto_model.h>
#include <goto-programs/read_goto_binary.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/c_types_util.h>
#include <util/cout_message.h>
#include <util/expr.h>
#include <util/expr_initializer.h>
#include <util/irep.h>
#include <util/mp_arith.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string_constant.h>

symbol_analyzert::symbol_analyzert(
  const symbol_tablet &st,
  gdb_apit &gdb,
  message_handlert &handler)
  : messaget(handler),
    gdb_api(gdb),
    ns(st),
    c_converter(ns, expr2c_configurationt::clean_configuration),
    id_counter(0)
{
}

void symbol_analyzert::analyse_symbol(const std::string &symbol_name)
{
  const symbolt symbol = ns.lookup(symbol_name);
  const symbol_exprt symbol_expr(symbol.name, symbol.type);

  if(is_c_char_pointer(symbol.type))
  {
    process_char_pointer(symbol_expr, symbol.location);
  }
  else if(is_void_pointer(symbol.type))
  {
    const exprt target_expr =
      fill_void_pointer_with_values(symbol_expr, symbol.location);

    add_assignment(symbol_expr, target_expr);
  }
  else if(is_pointer(symbol.type))
  {
    const std::string memory_location = gdb_api.get_memory(symbol_name);

    if(memory_location != "0x0")
    {
      const exprt target_symbol = process_any_pointer_target(
        symbol_expr, memory_location, symbol.location);
      const address_of_exprt reference_to_target(target_symbol);
      add_assignment(symbol_expr, reference_to_target);
    }
    else
    {
      const exprt null_ptr = zero_initializer(symbol.type, symbol.location, ns);
      add_assignment(symbol_expr, null_ptr);
    }
  }
  else
  {
    const typet target_type = ns.follow(symbol.type);
    const exprt target_expr = fill_expr_with_values(
      symbol_name,
      zero_initializer(target_type, symbol.location, ns),
      target_type,
      symbol.location);

    if(is_struct(target_type))
    {
      const struct_typet structt = to_struct_type(target_type);

      for(std::size_t i = 0; i < target_expr.operands().size(); ++i)
      {
        auto &member_declaration = structt.components()[i];
        if(!member_declaration.get_is_padding())
        {
          const auto &operand = target_expr.operands()[i];

          const symbol_exprt symbol_op(
            id2string(symbol.name) + "." +
              id2string(member_declaration.get(ID_name)),
            operand.type());
          add_assignment(symbol_op, operand);
        }
      }
    }
    else
    {
      add_assignment(symbol_expr, target_expr);
    }

    try
    {
      const std::string memory_location = gdb_api.get_memory("&" + symbol_name);
      values[memory_location] = symbol_expr;
    }
    catch(gdb_inaccessible_memoryt e)
    {
      warning() << "Couldn't access memory location for " << symbol_name << "\n"
                << "continue execution anyhow."
                << "You might want to check results for correctness!"
                << messaget::eom;
    }
  }
  process_outstanding_assignments();
}

std::string symbol_analyzert::get_code()
{
  return c_converter.convert(generated_code);
}

void symbol_analyzert::add_assignment(
  const symbol_exprt &symbol,
  const exprt &value)
{
  generated_code.add(code_assignt(symbol, value));
}

void symbol_analyzert::process_char_pointer(
  const symbol_exprt &symbol,
  const source_locationt &location)
{
  const std::string memory_location =
    gdb_api.get_memory(id2string(symbol.get_identifier()));
  const exprt target_object =
    declare_and_initalize_char_ptr(symbol, memory_location, location);

  add_assignment(symbol, target_object);
}

array_exprt create_char_array_from_string(
  std::string &values,
  const bitvector_typet &type,
  const source_locationt &location,
  const namespacet &ns)
{
  const std::regex single_char_pattern(
    "(?:(?:(?:\\\\)?([0-9]{3}))|([\\\\]{2}|\\S))");
  std::smatch result;
  std::vector<std::string> array_content;
  size_t content_size = type.get_width();
  while(regex_search(values, result, single_char_pattern))
  {
    if(!result[1].str().empty())
    {
      // Char are octal encoded in gdb output.
      mp_integer int_value = string2integer(result[1], OCTAL_SYSTEM);
      array_content.push_back(integer2binary(int_value, content_size));
    }
    else if(!result[2].str().empty())
    {
      char token = result[2].str()[0];
      array_content.push_back(integer2binary(token, content_size));
    }
    else
    {
      throw symbol_analysis_exceptiont(
        "It is not supposed that non group match");
    }
    values = result.suffix().str();
  }

  exprt size = from_integer(array_content.size(), size_type());
  array_typet new_array_type(type, size);
  array_exprt result_array =
    to_array_expr(zero_initializer(new_array_type, location, ns));

  for(size_t i = 0; i < array_content.size(); ++i)
  {
    result_array.operands()[i].set(ID_value, array_content[i]);
  }

  return result_array;
}

code_declt
symbol_analyzert::declare_instance(const std::string &prefix, const typet &type)
{
  std::string safe_prefix = prefix;
  std::replace(safe_prefix.begin(), safe_prefix.end(), '.', '_');
  std::replace(safe_prefix.begin(), safe_prefix.end(), '-', '_');
  std::replace(safe_prefix.begin(), safe_prefix.end(), '>', '_');
  std::replace(safe_prefix.begin(), safe_prefix.end(), '&', '_');
  std::replace(safe_prefix.begin(), safe_prefix.end(), '*', '_');
  safe_prefix.erase(
    std::remove(safe_prefix.begin(), safe_prefix.end(), '('),
    safe_prefix.end());
  safe_prefix.erase(
    std::remove(safe_prefix.begin(), safe_prefix.end(), ')'),
    safe_prefix.end());
  safe_prefix.erase(
    std::remove(safe_prefix.begin(), safe_prefix.end(), '['),
    safe_prefix.end());
  safe_prefix.erase(
    std::remove(safe_prefix.begin(), safe_prefix.end(), ']'),
    safe_prefix.end());
  safe_prefix.erase(
    std::remove(safe_prefix.begin(), safe_prefix.end(), ' '),
    safe_prefix.end());

  const std::string var_id = safe_prefix + "_" + std::to_string(id_counter);
  ++id_counter;
  const code_declt declaration(symbol_exprt(var_id, type));
  return declaration;
}

exprt symbol_analyzert::declare_and_initalize_char_ptr(
  const symbol_exprt &symbol,
  const std::string &memory_location,
  const source_locationt &location)
{
  const std::regex octal_encoding_pattern("(\\\\[0-9]{3})");

  auto it = values.find(memory_location);
  if(it == values.end())
  {
    std::string value = gdb_api.get_value(id2string(symbol.get_identifier()));

    exprt init = string_constantt(value);

    if(regex_search(value, octal_encoding_pattern))
    {
      bitvector_typet bv_type = to_bitvector_type(symbol.type().subtype());
      init = create_char_array_from_string(value, bv_type, location, ns);
    }

    code_declt target_object =
      declare_instance(id2string(symbol.get_identifier()), init.type());

    target_object.operands().resize(2);
    target_object.op1() = init;
    generated_code.add(target_object);
    const address_of_exprt deref_pointer(target_object.symbol());
    const exprt casted_if_needed =
      typecast_exprt::conditional_cast(deref_pointer, symbol.type());
    values[memory_location] = casted_if_needed;
    return casted_if_needed;
  }
  else
  {
    return it->second;
  }
}

exprt symbol_analyzert::process_any_pointer_target(
  const symbol_exprt &symbol,
  const std::string memory_location,
  const source_locationt &location)
{
  auto it = values.find(memory_location);
  if(it == values.end())
  {
    const place_holder_exprt recursion_breaker(memory_location);
    values[memory_location] = recursion_breaker;

    const typet target_type = ns.follow(symbol.type().subtype());
    const code_declt target_object = get_pointer_target(
      id2string(symbol.get_identifier()), target_type, location);
    generated_code.add(target_object);
    values[memory_location] = target_object.symbol();
    return target_object.symbol();
  }
  else
  {
    return it->second;
  }
}

code_declt symbol_analyzert::get_pointer_target(
  const std::string pointer_name,
  const typet &type,
  const source_locationt &location)
{
  code_declt declaration = declare_instance(pointer_name, type);

  const std::string deref_pointer = "(*" + pointer_name + ")";
  const exprt target_expr = fill_expr_with_values(
    deref_pointer, zero_initializer(type, location, ns), type, location);

  declaration.operands().resize(2);
  declaration.op1() = target_expr;
  return declaration;
}

exprt symbol_analyzert::fill_array_with_values(
  const std::string &symbol_id,
  exprt &array,
  const typet &type,
  const source_locationt &location)
{
  for(size_t i = 0; i < array.operands().size(); ++i)
  {
    const std::string cell_access = symbol_id + "[" + std::to_string(i) + "]";
    const typet target_type = ns.follow(array.operands()[i].type());
    if(is_c_char_pointer(target_type))
    {
      const std::string memory_location = gdb_api.get_memory(cell_access);
      const symbol_exprt char_ptr(cell_access, target_type);
      array.operands()[i] =
        declare_and_initalize_char_ptr(char_ptr, memory_location, location);
    }
    else
    {
      array.operands()[i] = fill_expr_with_values(
        cell_access, array.operands()[i], target_type, location);
    }
  }
  return array;
}

exprt symbol_analyzert::fill_expr_with_values(
  const std::string &symbol_id,
  exprt expr,
  const typet &type,
  const source_locationt &location)
{
  if(expr.is_constant() && (is_c_int_derivate(type) || is_c_char(type)))
  {
    const std::string value = gdb_api.get_value(symbol_id);
    const mp_integer int_rep = string2integer(value, DECIMAL_SYSTEM);
    return from_integer(int_rep, type);
  }
  else if(expr.is_constant() && is_c_bool(type))
  {
    const std::string value = gdb_api.get_value(symbol_id);
    return from_c_boolean_value(value, type);
  }
  else if(expr.is_constant() && is_c_enum(expr.type()))
  {
    const std::string value = gdb_api.get_value(symbol_id);
    return convert_memeber_name_to_enum_value(
      value, to_c_enum_type(expr.type()));
  }
  else if(is_struct(type))
  {
    return fill_struct_with_values(symbol_id, expr, type, location);
  }
  else if(is_array(type))
  {
    expr = fill_array_with_values(symbol_id, expr, type, location);
  }
  else
  {
    throw symbol_analysis_exceptiont(
      "unexpected thing:  " + expr.pretty() + "\nexception end\n");
  }
  return expr;
}

exprt symbol_analyzert::fill_char_struct_member_with_values(
  const symbol_exprt &field_access,
  const exprt &default_expr,
  const source_locationt &location)
{
  const std::string memory_location =
    gdb_api.get_memory(id2string(field_access.get_identifier()));
  if(memory_location != "0x0")
  {
    return declare_and_initalize_char_ptr(
      field_access, memory_location, location);
  }
  return default_expr;
}

exprt symbol_analyzert::fill_struct_with_values(
  const std::string &symbol_id,
  exprt &expr,
  const typet &type,
  const source_locationt &location)
{
  const struct_typet structt = to_struct_type(type);
  for(size_t i = 0; i < expr.operands().size(); ++i)
  {
    exprt &operand = expr.operands()[i];
    const typet &resolved_type = ns.follow(operand.type());
    if(!structt.components()[i].get_is_padding())
    {
      std::string field_access =
        symbol_id + "." + id2string(structt.components()[i].get_name());
      symbol_exprt field_symbol(field_access, resolved_type);

      if(is_c_char_pointer(resolved_type))
      {
        operand =
          fill_char_struct_member_with_values(field_symbol, operand, location);
      }
      else if(is_void_pointer(resolved_type))
      {
        operand = fill_void_pointer_with_values(field_symbol, location);
      }
      else if(is_struct(resolved_type))
      {
        code_declt declaration = declare_instance(field_access, resolved_type);

        const exprt target_expr = fill_expr_with_values(
          field_access,
          zero_initializer(resolved_type, location, ns),
          resolved_type,
          location);

        declaration.operands().resize(2);
        declaration.op1() = target_expr;
        generated_code.add(declaration);
        operand = declaration.symbol();
      }
      else if(is_pointer(resolved_type))
      {
        const std::string memory_location = gdb_api.get_memory(field_access);

        if(memory_location != "0x0")
        {
          const exprt target_sym =
            process_any_pointer_target(field_symbol, memory_location, location);

          if(target_sym.id() == ID_skip_initialize)
          {
            outstanding_assigns[field_symbol] =
              id2string(target_sym.get(ID_identifier));
          }
          else
          {
            operand = address_of_exprt(target_sym);
          }
        }
      }
      else if(is_array(resolved_type))
      {
        operand = fill_array_with_values(
          field_access, operand, resolved_type, location);
      }
      else
      {
        const std::string value = gdb_api.get_value(field_access);

        if(is_c_int_derivate(resolved_type))
        {
          const mp_integer int_rep = string2integer(value, DECIMAL_SYSTEM);
          const constant_exprt constant = from_integer(int_rep, operand.type());
          expr.operands()[i] = constant;
        }
      }
    }
  }
  return expr;
}

exprt symbol_analyzert::fill_void_pointer_with_values(
  const symbol_exprt &pointer_symbol,
  const source_locationt &location)
{
  const std::string &pointer_name = id2string(pointer_symbol.get_identifier());
  const std::string &char_casted = "(char *)" + pointer_name;
  exprt zero_ptr = zero_initializer(pointer_symbol.type(), location, ns);

  try
  {
    const typet &new_char_pointer = pointer_type(char_type());
    const symbol_exprt char_access_symbol(char_casted, new_char_pointer);

    const std::string memory_location = gdb_api.get_memory(pointer_name);

    if(memory_location == "0x0")
    {
      return zero_ptr;
    }
    return declare_and_initalize_char_ptr(
      char_access_symbol, memory_location, location);
  }
  catch(gdb_inaccessible_memoryt)
  {
    // It is not directly what is supposed to happen,
    // but doesn't corupt gdbs process state. So it's save to continue.
    // Anyhow, you should inspect the result and value of field_access
    // manually before using the state for verifcation.
    // Field access stays zero initalized.
    warning() << "Could not deal with void pointer: " << pointer_name
              << "\nThe value is potential unsafe and need review\n"
              << messaget::eom;
  }

  return zero_ptr;
}

void symbol_analyzert::process_outstanding_assignments()
{
  for(auto it = outstanding_assigns.begin(); it != outstanding_assigns.end();
      ++it)
  {
    const address_of_exprt reference_to_target(values[it->second]);
    generated_code.add(code_assignt(it->first, reference_to_target));
  }
}
#endif

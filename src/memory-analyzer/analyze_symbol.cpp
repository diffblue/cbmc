/*******************************************************************\

Module: Symbol Analyzer

Author: Malte Mues <mail.mues@gmail.com>
        Daniel Poetzl

\*******************************************************************/

#include "analyze_symbol.h"

#include <util/c_types.h>
#include <util/c_types_util.h>
#include <util/config.h>
#include <util/expr_initializer.h>
#include <util/string_constant.h>

gdb_value_extractort::gdb_value_extractort(
  const symbol_tablet &symbol_table,
  const char *binary)
  : gdb_api(binary),
    symbol_table(symbol_table),
    ns(symbol_table),
    c_converter(ns, expr2c_configurationt::clean_configuration),
    allocate_objects(ID_C, source_locationt(), irep_idt{}, this->symbol_table)
{
}

void gdb_value_extractort::analyze_symbols(const std::vector<irep_idt> &symbols)
{
  // record addresses of given symbols
  for(const auto &id : symbols)
  {
    const symbol_exprt &symbol_expr = ns.lookup(id).symbol_expr();
    const address_of_exprt aoe(symbol_expr);

    const std::string c_expr = c_converter.convert(aoe);
    const pointer_valuet &value = gdb_api.get_memory(c_expr);
    CHECK_RETURN(value.pointee.empty() || (id == value.pointee));

    values.insert({value.address, symbol_expr});
  }

  for(const auto &id : symbols)
  {
    analyze_symbol(id);
  }
}

void gdb_value_extractort::analyze_symbol(const irep_idt &symbol_name)
{
  const symbolt &symbol = ns.lookup(symbol_name);
  const symbol_exprt symbol_expr = symbol.symbol_expr();

  try
  {
    const typet target_type = symbol.type;

    const auto zero_expr = zero_initializer(target_type, symbol.location, ns);
    CHECK_RETURN(zero_expr);

    const exprt target_expr =
      get_expr_value(symbol_expr, *zero_expr, symbol.location);

    add_assignment(symbol_expr, target_expr);
  }
  catch(const gdb_interaction_exceptiont &e)
  {
    throw analysis_exceptiont(e.what());
  }

  process_outstanding_assignments();
}

/// Get memory snapshot as C code
std::string gdb_value_extractort::get_snapshot_as_c_code()
{
  code_blockt generated_code;

  allocate_objects.declare_created_symbols(generated_code);

  for(auto const &pair : assignments)
  {
    generated_code.add(code_assignt(pair.first, pair.second));
  }

  return c_converter.convert(generated_code);
}

/// Get memory snapshot as symbol table
symbol_tablet gdb_value_extractort::get_snapshot_as_symbol_table()
{
  symbol_tablet snapshot;

  for(const auto &pair : assignments)
  {
    const symbol_exprt &symbol_expr = to_symbol_expr(pair.first);
    const irep_idt id = symbol_expr.get_identifier();

    INVARIANT(symbol_table.has_symbol(id), "symbol must exist in symbol table");

    const symbolt &symbol = symbol_table.lookup_ref(id);

    symbolt snapshot_symbol(symbol);
    snapshot_symbol.value = pair.second;

    snapshot.insert(snapshot_symbol);
  }

  // Also add type symbols to the snapshot
  for(const auto &pair : symbol_table)
  {
    const symbolt &symbol = pair.second;

    if(symbol.is_type)
    {
      snapshot.insert(symbol);
    }
  }

  return snapshot;
}

void gdb_value_extractort::add_assignment(const exprt &lhs, const exprt &value)
{
  assignments.push_back(std::make_pair(lhs, value));
}

exprt gdb_value_extractort::get_char_pointer_value(
  const exprt &expr,
  const memory_addresst &memory_location,
  const source_locationt &location)
{
  PRECONDITION(expr.type().id() == ID_pointer);
  PRECONDITION(is_c_char_type(expr.type().subtype()));
  PRECONDITION(!memory_location.is_null());

  auto it = values.find(memory_location);

  if(it == values.end())
  {
    std::string c_expr = c_converter.convert(expr);
    pointer_valuet value = gdb_api.get_memory(c_expr);
    CHECK_RETURN(value.string);

    string_constantt init(*value.string);
    CHECK_RETURN(to_array_type(init.type()).is_complete());

    symbol_exprt dummy("tmp", pointer_type(init.type()));
    code_blockt assignments;

    const symbol_exprt new_symbol =
      to_symbol_expr(allocate_objects.allocate_automatic_local_object(
        assignments, dummy, init.type()));

    add_assignment(new_symbol, init);

    values.insert(std::make_pair(memory_location, new_symbol));

    return new_symbol;
  }
  else
  {
    return it->second;
  }
}

exprt gdb_value_extractort::get_non_char_pointer_value(
  const exprt &expr,
  const memory_addresst &memory_location,
  const source_locationt &location)
{
  PRECONDITION(expr.type().id() == ID_pointer);
  PRECONDITION(!is_c_char_type(expr.type().subtype()));
  PRECONDITION(!memory_location.is_null());

  auto it = values.find(memory_location);

  if(it == values.end())
  {
    values.insert(std::make_pair(memory_location, nil_exprt()));

    const typet target_type = expr.type().subtype();

    symbol_exprt dummy("tmp", expr.type());
    code_blockt assignments;

    const symbol_exprt new_symbol =
      to_symbol_expr(allocate_objects.allocate_automatic_local_object(
        assignments, dummy, target_type));

    dereference_exprt dereference_expr(expr);

    const auto zero_expr = zero_initializer(target_type, location, ns);
    CHECK_RETURN(zero_expr);

    const exprt target_expr =
      get_expr_value(dereference_expr, *zero_expr, location);

    // add assignment of value to newly created symbol
    add_assignment(new_symbol, target_expr);

    values[memory_location] = new_symbol;

    return new_symbol;
  }
  else
  {
    return it->second;
  }
}

exprt gdb_value_extractort::get_pointer_value(
  const exprt &expr,
  const exprt &zero_expr,
  const source_locationt &location)
{
  PRECONDITION(zero_expr.id() == ID_constant);

  PRECONDITION(expr.type().id() == ID_pointer);
  PRECONDITION(expr.type() == zero_expr.type());

  std::string c_expr = c_converter.convert(expr);
  const pointer_valuet value = gdb_api.get_memory(c_expr);

  const auto memory_location = value.address;

  if(!memory_location.is_null())
  {
    if(is_c_char_type(expr.type().subtype()))
    {
      return get_char_pointer_value(expr, memory_location, location);
    }
    else
    {
      const exprt target_expr =
        get_non_char_pointer_value(expr, memory_location, location);

      if(target_expr.id() == ID_nil)
      {
        outstanding_assignments[expr] = memory_location;
      }
      else
      {
        return address_of_exprt(target_expr);
      }
    }
  }

  return zero_expr;
}

exprt gdb_value_extractort::get_array_value(
  const exprt &expr,
  const exprt &array,
  const source_locationt &location)
{
  PRECONDITION(array.id() == ID_array);

  PRECONDITION(expr.type().id() == ID_array);
  PRECONDITION(expr.type() == array.type());

  exprt new_array(array);

  for(size_t i = 0; i < new_array.operands().size(); ++i)
  {
    const index_exprt index_expr(expr, from_integer(i, index_type()));

    exprt &operand = new_array.operands()[i];

    operand = get_expr_value(index_expr, operand, location);
  }

  return new_array;
}

exprt gdb_value_extractort::get_expr_value(
  const exprt &expr,
  const exprt &zero_expr,
  const source_locationt &location)
{
  PRECONDITION(expr.type() == zero_expr.type());

  const typet &type = expr.type();
  PRECONDITION(type.id() != ID_struct);

  if(is_c_integral_type(type))
  {
    INVARIANT(zero_expr.is_constant(), "zero initializer is a constant");

    return from_integer(string2integer(get_gdb_value(expr)), expr.type());
  }
  else if(is_c_char_type(type))
  {
    INVARIANT(zero_expr.is_constant(), "zero initializer is a constant");

    return zero_expr; // currently left at 0
  }
  else if(type.id() == ID_c_bool)
  {
    INVARIANT(zero_expr.is_constant(), "zero initializer is a constant");

    return from_c_boolean_value(id2boolean(get_gdb_value(expr)), type);
  }
  else if(type.id() == ID_c_enum)
  {
    INVARIANT(zero_expr.is_constant(), "zero initializer is a constant");

    return convert_member_name_to_enum_value(
      get_gdb_value(expr), to_c_enum_type(type));
  }
  else if(type.id() == ID_struct_tag)
  {
    return get_struct_value(expr, zero_expr, location);
  }
  else if(type.id() == ID_array)
  {
    return get_array_value(expr, zero_expr, location);
  }
  else if(type.id() == ID_pointer)
  {
    INVARIANT(zero_expr.is_constant(), "zero initializer is a constant");

    return get_pointer_value(expr, zero_expr, location);
  }
  UNIMPLEMENTED;
}

exprt gdb_value_extractort::get_struct_value(
  const exprt &expr,
  const exprt &zero_expr,
  const source_locationt &location)
{
  PRECONDITION(zero_expr.id() == ID_struct);

  PRECONDITION(expr.type().id() == ID_struct_tag);
  PRECONDITION(expr.type() == zero_expr.type());

  exprt new_expr(zero_expr);

  const struct_tag_typet &struct_tag_type = to_struct_tag_type(expr.type());
  const struct_typet &struct_type = ns.follow_tag(struct_tag_type);

  for(size_t i = 0; i < new_expr.operands().size(); ++i)
  {
    const struct_typet::componentt &component = struct_type.components()[i];

    if(component.get_is_padding() || component.type().id() == ID_code)
    {
      continue;
    }

    exprt &operand = new_expr.operands()[i];
    member_exprt member_expr(expr, component);

    operand = get_expr_value(member_expr, operand, location);
  }

  return new_expr;
}

void gdb_value_extractort::process_outstanding_assignments()
{
  for(const auto &pair : outstanding_assignments)
  {
    const address_of_exprt aoe(values[pair.second]);
    add_assignment(pair.first, aoe);
  }
}

std::string gdb_value_extractort::get_gdb_value(const exprt &expr)
{
  return gdb_api.get_value(c_converter.convert(expr));
}

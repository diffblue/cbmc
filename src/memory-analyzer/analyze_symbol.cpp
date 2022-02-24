/*******************************************************************\

Module: Symbol Analyzer

Author: Malte Mues <mail.mues@gmail.com>
        Daniel Poetzl

\*******************************************************************/

#include "analyze_symbol.h"

#include <util/c_types.h>
#include <util/c_types_util.h>
#include <util/expr_initializer.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/string2int.h>
#include <util/string_constant.h>
#include <util/string_utils.h>

#include <climits>
#include <cstdlib>

gdb_value_extractort::gdb_value_extractort(
  const symbol_tablet &symbol_table,
  const std::vector<std::string> &args)
  : gdb_api(args),
    symbol_table(symbol_table),
    ns(symbol_table),
    c_converter(ns, expr2c_configurationt::clean_configuration),
    allocate_objects(ID_C, source_locationt(), irep_idt{}, this->symbol_table)
{
}

gdb_value_extractort::memory_scopet::memory_scopet(
  const memory_addresst &begin,
  const mp_integer &byte_size,
  const irep_idt &name)
  : begin_int(safe_string2size_t(begin.address_string, 0)),
    byte_size(byte_size),
    name(name)
{
}

size_t gdb_value_extractort::memory_scopet::address2size_t(
  const memory_addresst &point) const
{
  return safe_string2size_t(point.address_string, 0);
}

mp_integer gdb_value_extractort::memory_scopet::distance(
  const memory_addresst &point,
  mp_integer member_size) const
{
  auto point_int = address2size_t(point);
  CHECK_RETURN(check_containment(point_int));
  return (point_int - begin_int) / member_size;
}

std::vector<gdb_value_extractort::memory_scopet>::iterator
gdb_value_extractort::find_dynamic_allocation(irep_idt name)
{
  return std::find_if(
    dynamically_allocated.begin(),
    dynamically_allocated.end(),
    [&name](const memory_scopet &scope) { return scope.id() == name; });
}

std::vector<gdb_value_extractort::memory_scopet>::iterator
gdb_value_extractort::find_dynamic_allocation(const memory_addresst &point)
{
  return std::find_if(
    dynamically_allocated.begin(),
    dynamically_allocated.end(),
    [&point](const memory_scopet &memory_scope) {
      return memory_scope.contains(point);
    });
}

mp_integer gdb_value_extractort::get_malloc_size(irep_idt name)
{
  const auto scope_it = find_dynamic_allocation(name);
  if(scope_it == dynamically_allocated.end())
    return 1;
  else
    return scope_it->size();
}

optionalt<std::string> gdb_value_extractort::get_malloc_pointee(
  const memory_addresst &point,
  mp_integer member_size)
{
  const auto scope_it = find_dynamic_allocation(point);
  if(scope_it == dynamically_allocated.end())
    return {};

  const auto pointer_distance = scope_it->distance(point, member_size);
  return id2string(scope_it->id()) +
         (pointer_distance > 0 ? "+" + integer2string(pointer_distance) : "");
}

mp_integer gdb_value_extractort::get_type_size(const typet &type) const
{
  const auto maybe_size = pointer_offset_bits(type, ns);
  CHECK_RETURN(maybe_size.has_value());
  return *maybe_size / CHAR_BIT;
}

void gdb_value_extractort::analyze_symbols(const std::vector<irep_idt> &symbols)
{
  // record addresses of given symbols
  for(const auto &id : symbols)
  {
    const symbolt &symbol = ns.lookup(id);
    if(
      symbol.type.id() != ID_pointer ||
      is_c_char_type(to_pointer_type(symbol.type).base_type()))
    {
      const symbol_exprt &symbol_expr = ns.lookup(id).symbol_expr();
      const address_of_exprt aoe(symbol_expr);

      const std::string c_expr = c_converter.convert(aoe);
      const pointer_valuet &value = gdb_api.get_memory(c_expr);
      CHECK_RETURN(value.pointee.empty() || (id == value.pointee));

      memory_map[id] = value;
    }
    else
    {
      const std::string c_symbol = c_converter.convert(symbol.symbol_expr());
      const pointer_valuet &symbol_value = gdb_api.get_memory(c_symbol);
      size_t symbol_size = gdb_api.query_malloc_size(c_symbol);

      if(symbol_size > 1)
        dynamically_allocated.emplace_back(
          symbol_value.address, symbol_size, id);
      memory_map[id] = symbol_value;
    }
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
  if(assignments.count(lhs) == 0)
    assignments.emplace(std::make_pair(lhs, value));
}

exprt gdb_value_extractort::get_char_pointer_value(
  const exprt &expr,
  const memory_addresst &memory_location,
  const source_locationt &location)
{
  PRECONDITION(expr.type().id() == ID_pointer);
  PRECONDITION(is_c_char_type(to_pointer_type(expr.type()).base_type()));
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

    // check that we are returning objects of the right type
    CHECK_RETURN(
      to_array_type(new_symbol.type()).element_type() ==
      to_pointer_type(expr.type()).base_type());
    return new_symbol;
  }
  else
  {
    CHECK_RETURN(
      to_array_type(it->second.type()).element_type() ==
      to_pointer_type(expr.type()).base_type());
    return it->second;
  }
}

exprt gdb_value_extractort::get_pointer_to_member_value(
  const exprt &expr,
  const pointer_valuet &pointer_value,
  const source_locationt &location)
{
  PRECONDITION(expr.type().id() == ID_pointer);
  const auto &memory_location = pointer_value.address;
  std::string memory_location_string = memory_location.string();
  PRECONDITION(memory_location_string != "0x0");
  PRECONDITION(!pointer_value.pointee.empty());

  std::string struct_name;
  size_t member_offset;
  if(pointer_value.has_known_offset())
  {
    std::string member_offset_string;
    split_string(
      pointer_value.pointee, '+', struct_name, member_offset_string, true);
    member_offset = safe_string2size_t(member_offset_string);
  }
  else
  {
    struct_name = pointer_value.pointee;
    member_offset = 0;
  }

  const symbolt *struct_symbol = symbol_table.lookup(struct_name);
  DATA_INVARIANT(struct_symbol != nullptr, "unknown struct");

  if(!has_known_memory_location(struct_name))
  {
    memory_map[struct_name] = gdb_api.get_memory(struct_name);
    analyze_symbol(irep_idt{struct_name});
  }

  const auto &struct_symbol_expr = struct_symbol->symbol_expr();
  if(struct_symbol->type.id() == ID_array)
  {
    return index_exprt{
      struct_symbol_expr,
      from_integer(
        member_offset / get_type_size(to_pointer_type(expr.type()).base_type()),
        index_type())};
  }
  if(struct_symbol->type.id() == ID_pointer)
  {
    return dereference_exprt{
      plus_exprt{struct_symbol_expr,
                 from_integer(member_offset, size_type()),
                 expr.type()}};
  }

  const auto maybe_member_expr = get_subexpression_at_offset(
    struct_symbol_expr,
    member_offset,
    to_pointer_type(expr.type()).base_type(),
    ns);
  DATA_INVARIANT(
    maybe_member_expr.has_value(), "structure doesn't have member");

  // check that we return the right type
  CHECK_RETURN(
    maybe_member_expr->type() == to_pointer_type(expr.type()).base_type());
  return *maybe_member_expr;
}

exprt gdb_value_extractort::get_pointer_to_function_value(
  const exprt &expr,
  const pointer_valuet &pointer_value,
  const source_locationt &location)
{
  PRECONDITION(expr.type().id() == ID_pointer);
  PRECONDITION(to_pointer_type(expr.type()).base_type().id() == ID_code);
  PRECONDITION(!pointer_value.address.is_null());

  const auto &function_name = pointer_value.pointee;
  CHECK_RETURN(!function_name.empty());
  const auto function_symbol = symbol_table.lookup(function_name);
  if(function_symbol == nullptr)
  {
    throw invalid_input_exceptiont{
      "input source code does not contain function: " + function_name};
  }
  CHECK_RETURN(function_symbol->type.id() == ID_code);
  return function_symbol->symbol_expr();
}

exprt gdb_value_extractort::get_non_char_pointer_value(
  const exprt &expr,
  const pointer_valuet &value,
  const source_locationt &location)
{
  PRECONDITION(expr.type().id() == ID_pointer);
  PRECONDITION(!is_c_char_type(to_pointer_type(expr.type()).base_type()));
  const auto &memory_location = value.address;
  PRECONDITION(!memory_location.is_null());

  auto it = values.find(memory_location);

  if(it == values.end())
  {
    if(!value.pointee.empty() && value.pointee != c_converter.convert(expr))
    {
      analyze_symbol(value.pointee);
      const auto pointee_symbol = symbol_table.lookup(value.pointee);
      CHECK_RETURN(pointee_symbol != nullptr);
      const auto pointee_symbol_expr = pointee_symbol->symbol_expr();
      return pointee_symbol_expr;
    }

    values.insert(std::make_pair(memory_location, nil_exprt()));

    const typet target_type = to_pointer_type(expr.type()).base_type();

    symbol_exprt dummy("tmp", expr.type());
    code_blockt assignments;

    const auto zero_expr = zero_initializer(target_type, location, ns);
    CHECK_RETURN(zero_expr);

    // Check if pointer was dynamically allocated (via malloc). If so we will
    // replace the pointee with a static array filled with values stored at the
    // expected positions. Since the allocated size is over-approximation we may
    // end up querying pass the allocated bounds and building larger array with
    // meaningless values.
    mp_integer allocated_size = get_malloc_size(c_converter.convert(expr));
    // get the sizeof(target_type) and thus the number of elements
    const auto number_of_elements = allocated_size / get_type_size(target_type);
    if(allocated_size != 1 && number_of_elements > 1)
    {
      array_exprt::operandst elements;
      // build the operands by querying for an index expression
      for(size_t i = 0; i < number_of_elements; i++)
      {
        const auto sub_expr_value = get_expr_value(
          index_exprt{expr, from_integer(i, index_type())},
          *zero_expr,
          location);
        elements.push_back(sub_expr_value);
      }
      CHECK_RETURN(elements.size() == number_of_elements);

      // knowing the number of elements we can build the type
      const typet target_array_type =
        array_typet{target_type, from_integer(elements.size(), index_type())};

      array_exprt new_array{elements, to_array_type(target_array_type)};

      // allocate a new symbol for the temporary static array
      symbol_exprt array_dummy("tmp", pointer_type(target_array_type));
      const auto array_symbol =
        allocate_objects.allocate_automatic_local_object(
          assignments, array_dummy, target_array_type);

      // add assignment of value to newly created symbol
      add_assignment(array_symbol, new_array);
      values[memory_location] = array_symbol;
      CHECK_RETURN(array_symbol.type().id() == ID_array);
      return array_symbol;
    }

    const symbol_exprt new_symbol =
      to_symbol_expr(allocate_objects.allocate_automatic_local_object(
        assignments, dummy, target_type));

    dereference_exprt dereference_expr(expr);

    const exprt target_expr =
      get_expr_value(dereference_expr, *zero_expr, location);
    // add assignment of value to newly created symbol
    add_assignment(new_symbol, target_expr);

    values[memory_location] = new_symbol;

    return new_symbol;
  }
  else
  {
    const auto &known_value = it->second;
    const auto &expected_type = to_pointer_type(expr.type()).base_type();
    if(find_dynamic_allocation(memory_location) != dynamically_allocated.end())
      return known_value;
    if(known_value.is_not_nil() && known_value.type() != expected_type)
    {
      return symbol_exprt{to_symbol_expr(known_value).get_identifier(),
                          expected_type};
    }
    return known_value;
  }
}

bool gdb_value_extractort::points_to_member(
  pointer_valuet &pointer_value,
  const pointer_typet &expected_type)
{
  if(pointer_value.has_known_offset())
    return true;

  if(pointer_value.pointee.empty())
  {
    const auto maybe_pointee = get_malloc_pointee(
      pointer_value.address, get_type_size(expected_type.base_type()));
    if(maybe_pointee.has_value())
      pointer_value.pointee = *maybe_pointee;
    if(pointer_value.pointee.find("+") != std::string::npos)
      return true;
  }

  const symbolt *pointee_symbol = symbol_table.lookup(pointer_value.pointee);
  if(pointee_symbol == nullptr)
    return false;
  const auto &pointee_type = pointee_symbol->type;
  return pointee_type.id() == ID_struct_tag ||
         pointee_type.id() == ID_union_tag || pointee_type.id() == ID_array ||
         pointee_type.id() == ID_struct || pointee_type.id() == ID_union;
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
  const auto known_pointer = memory_map.find(c_expr);

  pointer_valuet value = (known_pointer == memory_map.end() ||
                          known_pointer->second.pointee == c_expr)
                           ? gdb_api.get_memory(c_expr)
                           : known_pointer->second;
  if(!value.valid)
    return zero_expr;

  const auto memory_location = value.address;

  if(!memory_location.is_null())
  {
    // pointers-to-char can point to members as well, e.g. char[]
    if(points_to_member(value, to_pointer_type(expr.type())))
    {
      const auto target_expr =
        get_pointer_to_member_value(expr, value, location);
      CHECK_RETURN(target_expr.is_not_nil());
      const address_of_exprt result_expr{target_expr};
      CHECK_RETURN(result_expr.type() == zero_expr.type());
      return std::move(result_expr);
    }

    // pointer to function
    if(to_pointer_type(expr.type()).base_type().id() == ID_code)
    {
      const auto target_expr =
        get_pointer_to_function_value(expr, value, location);
      CHECK_RETURN(target_expr.is_not_nil());
      const address_of_exprt result_expr{target_expr};
      CHECK_RETURN(result_expr.type() == zero_expr.type());
      return std::move(result_expr);
    }

    // non-member: split for char/non-char
    const auto target_expr =
      is_c_char_type(to_pointer_type(expr.type()).base_type())
        ? get_char_pointer_value(expr, memory_location, location)
        : get_non_char_pointer_value(expr, value, location);

    // postpone if we cannot resolve now
    if(target_expr.is_nil())
    {
      outstanding_assignments[expr] = memory_location;
      return zero_expr;
    }

    // the pointee was (probably) dynamically allocated (but the allocation
    // would not be visible in the snapshot) so we pretend it is statically
    // allocated (we have the value) and return address to the first element
    // of the array (instead of the array as char*)
    if(target_expr.type().id() == ID_array)
    {
      const auto result_indexed_expr = get_subexpression_at_offset(
        target_expr, 0, to_pointer_type(zero_expr.type()).base_type(), ns);
      CHECK_RETURN(result_indexed_expr.has_value());
      if(result_indexed_expr->type() == zero_expr.type())
        return *result_indexed_expr;
      const address_of_exprt result_expr{*result_indexed_expr};
      CHECK_RETURN(result_expr.type() == zero_expr.type());
      return std::move(result_expr);
    }

    // if the types match return right away
    if(target_expr.type() == zero_expr.type())
      return target_expr;

    // otherwise the address of target should type-match
    const address_of_exprt result_expr{target_expr};
    if(result_expr.type() != zero_expr.type())
      return typecast_exprt{result_expr, zero_expr.type()};
    return std::move(result_expr);
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

    std::string c_expr = c_converter.convert(expr);
    const auto maybe_value = gdb_api.get_value(c_expr);
    if(!maybe_value.has_value())
      return zero_expr;
    const std::string value = *maybe_value;

    const mp_integer int_rep = string2integer(value);

    return from_integer(int_rep, type);
  }
  else if(is_c_char_type(type))
  {
    INVARIANT(zero_expr.is_constant(), "zero initializer is a constant");

    // check the char-value and return as bitvector-type value
    std::string c_expr = c_converter.convert(expr);
    const auto maybe_value = gdb_api.get_value(c_expr);
    if(!maybe_value.has_value() || maybe_value->empty())
      return zero_expr;
    const std::string value = *maybe_value;

    const mp_integer int_rep = value[0];
    return from_integer(int_rep, type);
  }
  else if(type.id() == ID_c_bool)
  {
    INVARIANT(zero_expr.is_constant(), "zero initializer is a constant");

    std::string c_expr = c_converter.convert(expr);
    const auto maybe_value = gdb_api.get_value(c_expr);
    if(!maybe_value.has_value())
      return zero_expr;
    const std::string value = *maybe_value;

    return from_c_boolean_value(id2boolean(value), type);
  }
  else if(type.id() == ID_c_enum)
  {
    INVARIANT(zero_expr.is_constant(), "zero initializer is a constant");

    std::string c_expr = c_converter.convert(expr);
    const auto maybe_value = gdb_api.get_value(c_expr);
    if(!maybe_value.has_value())
      return zero_expr;
    const std::string value = *maybe_value;

    return convert_member_name_to_enum_value(value, to_c_enum_type(type));
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
  else if(type.id() == ID_union_tag)
  {
    return get_union_value(expr, zero_expr, location);
  }
  UNREACHABLE;
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

exprt gdb_value_extractort::get_union_value(
  const exprt &expr,
  const exprt &zero_expr,
  const source_locationt &location)
{
  PRECONDITION(zero_expr.id() == ID_union);

  PRECONDITION(expr.type().id() == ID_union_tag);
  PRECONDITION(expr.type() == zero_expr.type());

  exprt new_expr(zero_expr);

  const union_tag_typet &union_tag_type = to_union_tag_type(expr.type());
  const union_typet &union_type = ns.follow_tag(union_tag_type);

  CHECK_RETURN(new_expr.operands().size() == 1);
  const union_typet::componentt &component = union_type.components()[0];
  auto &operand = new_expr.operands()[0];
  operand = get_expr_value(member_exprt{expr, component}, operand, location);
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
  std::string c_expr = c_converter.convert(expr);
  const auto maybe_value = gdb_api.get_value(c_expr);
  CHECK_RETURN(maybe_value.has_value());
  return *maybe_value;
}

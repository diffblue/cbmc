/*******************************************************************\

Module: Java lambda code synthesis

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Java lambda code synthesis

#include "lambda_synthesis.h"

#include "java_bytecode_convert_method.h"
#include "java_bytecode_parse_tree.h"
#include "java_types.h"
#include "java_utils.h"
#include "synthetic_methods_map.h"

#include <util/message.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/symbol_table.h>

#include <string.h>

static std::string escape_symbol_special_chars(std::string input)
{
  for(auto &c : input)
  {
    if(c == '$' || c == ':' || c == '.')
      c = '_';
  }
  return input;
}

irep_idt lambda_synthetic_class_name(
  const irep_idt &method_identifier,
  std::size_t instruction_address)
{
  return "java::lambda_synthetic_class$" +
         escape_symbol_special_chars(
           id2string(strip_java_namespace_prefix(method_identifier))) +
         "$" + std::to_string(instruction_address);
}

/// Retrieves the symbol of the lambda method associated with the given
/// lambda method handle (bootstrap method).
/// \param symbol_table: global symbol table
/// \param lambda_method_handles: Vector of lambda method handles (bootstrap
///   methods) of the class where the lambda is called
/// \param index: Index of the lambda method handle in the vector
/// \return Symbol of the lambda method if the method handle has a known type
static optionalt<symbolt> get_lambda_method_symbol(
  const symbol_table_baset &symbol_table,
  const java_class_typet::java_lambda_method_handlest &lambda_method_handles,
  const size_t index)
{
  // Check if we don't have enough bootstrap methods to satisfy the requested
  // lambda. This could happen if we fail to parse one of the methods, or if
  // the class type is partly or entirely synthetic, such as the types created
  // internally by the string solver.
  if(index >= lambda_method_handles.size())
    return {};
  const irept &lambda_method_handle = lambda_method_handles.at(index);
  // If the lambda method handle has an unknown type, it does not refer to
  // any symbol (it has an empty identifier)
  if(!lambda_method_handle.id().empty())
    return symbol_table.lookup_ref(lambda_method_handle.id());
  return {};
}

static optionalt<irep_idt> lambda_method_name(
  const symbol_tablet &symbol_table,
  const irep_idt &method_identifier,
  const java_method_typet &dynamic_method_type)
{
  const namespacet ns{symbol_table};
  const auto &method_symbol = ns.lookup(method_identifier);
  const auto &declaring_class_symbol =
    ns.lookup(*declaring_class(method_symbol));

  const auto &class_type = to_java_class_type(declaring_class_symbol.type);
  const auto &lambda_method_handles = class_type.lambda_method_handles();
  auto lambda_handle_index =
    dynamic_method_type.get_int(ID_java_lambda_method_handle_index);
  const auto lambda_method_symbol = get_lambda_method_symbol(
    symbol_table, lambda_method_handles, lambda_handle_index);
  if(lambda_method_symbol)
    return lambda_method_symbol->name;
  return {};
}

static optionalt<irep_idt> interface_method_id(
  const symbol_tablet &symbol_table,
  const struct_tag_typet &functional_interface_tag,
  const irep_idt &method_identifier,
  const int instruction_address,
  const messaget &log)
{
  const namespacet ns{symbol_table};
  const java_class_typet &implemented_interface_type = [&] {
    const symbolt &implemented_interface_symbol =
      ns.lookup(functional_interface_tag.get_identifier());
    return to_java_class_type(implemented_interface_symbol.type);
  }();

  if(implemented_interface_type.get_is_stub())
  {
    log.debug() << "ignoring invokedynamic at " << method_identifier
                << " address " << instruction_address
                << " which produces a stub type "
                << functional_interface_tag.get_identifier() << messaget::eom;
    return {};
  }
  else if(implemented_interface_type.methods().size() != 1)
  {
    log.debug()
      << "ignoring invokedynamic at " << method_identifier << " address "
      << instruction_address << " which produces type "
      << functional_interface_tag.get_identifier()
      << " which should have exactly one abstract method but actually has "
      << implemented_interface_type.methods().size()
      << ". Note default methods are not supported yet."
      << "Also note methods declared in an inherited interface are not "
      << "supported either." << messaget::eom;
    return {};
  }
  return implemented_interface_type.methods().at(0).get_name();
}

symbolt synthetic_class_symbol(
  const irep_idt &synthetic_class_name,
  const irep_idt &lambda_method_name,
  const struct_tag_typet &functional_interface_tag,
  const java_method_typet &dynamic_method_type)
{
  java_class_typet synthetic_class_type;
  // Tag = name without 'java::' prefix, matching the convention used by
  // java_bytecode_convert_class.cpp
  synthetic_class_type.set_tag(
    strip_java_namespace_prefix(synthetic_class_name));
  synthetic_class_type.set_name(synthetic_class_name);
  synthetic_class_type.set_synthetic(true);
  synthetic_class_type.set(
    ID_java_lambda_method_identifier, lambda_method_name);
  struct_tag_typet base_tag("java::java.lang.Object");
  synthetic_class_type.add_base(base_tag);
  synthetic_class_type.add_base(functional_interface_tag);

  // Add the class fields:

  {
    java_class_typet::componentt base_field;
    const irep_idt base_field_name("@java.lang.Object");
    base_field.set_name(base_field_name);
    base_field.set_base_name(base_field_name);
    base_field.set_pretty_name(base_field_name);
    base_field.set_access(ID_private);
    base_field.type() = base_tag;
    synthetic_class_type.components().emplace_back(std::move(base_field));

    std::size_t field_idx = 0;
    for(const auto &param : dynamic_method_type.parameters())
    {
      irep_idt field_basename = "capture_" + std::to_string(field_idx++);

      java_class_typet::componentt new_field;
      new_field.set_name(field_basename);
      new_field.set_base_name(field_basename);
      new_field.set_pretty_name(field_basename);
      new_field.set_access(ID_private);
      new_field.type() = param.type();
      synthetic_class_type.components().emplace_back(std::move(new_field));
    }
  }

  symbolt synthetic_class_symbol = type_symbolt{synthetic_class_type};
  synthetic_class_symbol.name = synthetic_class_name;
  synthetic_class_symbol.mode = ID_java;
  return synthetic_class_symbol;
}

static symbolt constructor_symbol(
  synthetic_methods_mapt &synthetic_methods,
  const irep_idt &synthetic_class_name,
  java_method_typet constructor_type) // dynamic_method_type
{
  symbolt constructor_symbol;
  irep_idt constructor_name = id2string(synthetic_class_name) + ".<init>";
  constructor_symbol.name = constructor_name;
  constructor_symbol.pretty_name = constructor_symbol.name;
  constructor_symbol.base_name = "<init>";
  constructor_symbol.mode = ID_java;

  synthetic_methods[constructor_name] =
    synthetic_method_typet::INVOKEDYNAMIC_CAPTURE_CONSTRUCTOR;

  constructor_type.set_is_constructor();
  constructor_type.return_type() = empty_typet();

  size_t field_idx = 0;
  for(auto &param : constructor_type.parameters())
  {
    irep_idt param_basename = "param_" + std::to_string(field_idx++);
    param.set_base_name(param_basename);
    param.set_identifier(
      id2string(constructor_name) + "::" + id2string(param_basename));
  }

  java_method_typet::parametert constructor_this_param;
  constructor_this_param.set_this();
  constructor_this_param.set_base_name("this");
  constructor_this_param.set_identifier(id2string(constructor_name) + "::this");
  constructor_this_param.type() =
    java_reference_type(struct_tag_typet(synthetic_class_name));

  constructor_type.parameters().insert(
    constructor_type.parameters().begin(), constructor_this_param);

  constructor_symbol.type = constructor_type;
  set_declaring_class(constructor_symbol, synthetic_class_name);
  return constructor_symbol;
}

symbolt implemented_method_symbol(
  synthetic_methods_mapt &synthetic_methods,
  const symbolt &interface_method_symbol,
  const struct_tag_typet &functional_interface_tag,
  const irep_idt &synthetic_class_name)
{
  const std::string implemented_method_name = [&] {
    std::string implemented_method_name =
      id2string(interface_method_symbol.name);
    const std::string &functional_interface_tag_str =
      id2string(functional_interface_tag.get_identifier());
    INVARIANT(
      has_prefix(implemented_method_name, functional_interface_tag_str),
      "method names should be prefixed by their defining type");
    implemented_method_name.replace(
      0,
      functional_interface_tag_str.length(),
      id2string(synthetic_class_name));
    return implemented_method_name;
  }();

  symbolt implemented_method_symbol;
  implemented_method_symbol.name = implemented_method_name;
  synthetic_methods[implemented_method_symbol.name] =
    synthetic_method_typet::INVOKEDYNAMIC_METHOD;
  implemented_method_symbol.pretty_name = implemented_method_symbol.name;
  implemented_method_symbol.base_name = interface_method_symbol.base_name;
  implemented_method_symbol.mode = ID_java;
  implemented_method_symbol.type = interface_method_symbol.type;
  auto &implemented_method_type = to_code_type(implemented_method_symbol.type);
  implemented_method_type.parameters()[0].type() =
    java_reference_type(struct_tag_typet(synthetic_class_name));

  size_t field_idx = 0;
  for(auto &param : implemented_method_type.parameters())
  {
    irep_idt param_basename =
      field_idx == 0 ? "this" : "param_" + std::to_string(field_idx);
    param.set_base_name(param_basename);
    param.set_identifier(
      id2string(implemented_method_name) + "::" + id2string(param_basename));

    ++field_idx;
  }

  set_declaring_class(implemented_method_symbol, synthetic_class_name);
  return implemented_method_symbol;
}

// invokedynamic will be called with operands that should be stored in a
// synthetic object implementing the interface type that it returns. For
// example, "invokedynamic f(a, b, c) -> MyInterface" should result in the
// creation of the synthetic class:
// public class SyntheticCapture implements MyInterface {
//   private int a;
//   private float b;
//   private Other c;
//   public SyntheticCapture(int a, float b, Other c) {
//     this.a = a; this.b = b; this.c = c;
//   }
//   public void myInterfaceMethod(int d) {
//     f(a, b, c, d);
//   }
// }
// This method just creates the outline; the methods will be populated on
// demand via java_bytecode_languaget::convert_lazy_method.

// Check that we understand the lambda method handle; if we don't then
// we will not create a synthetic class at all, and the corresponding
// invoke instruction will return null when eventually converted by
// java_bytecode_convert_method.
void create_invokedynamic_synthetic_classes(
  const irep_idt &method_identifier,
  const java_bytecode_parse_treet::methodt::instructionst &instructions,
  symbol_tablet &symbol_table,
  synthetic_methods_mapt &synthetic_methods,
  message_handlert &message_handler)
{
  const messaget log{message_handler};

  for(const auto &instruction : instructions)
  {
    if(strcmp(bytecode_info[instruction.bytecode].mnemonic, "invokedynamic"))
      continue;
    const auto &dynamic_method_type =
      to_java_method_type(instruction.args.at(0).type());
    const auto lambda_method_name = ::lambda_method_name(
      symbol_table, method_identifier, dynamic_method_type);
    if(!lambda_method_name)
    {
      log.debug() << "ignoring invokedynamic at " << method_identifier
                  << " address " << instruction.address
                  << " with unknown handle type" << messaget::eom;
      continue;
    }
    const auto &functional_interface_tag = to_struct_tag_type(
      to_java_reference_type(dynamic_method_type.return_type()).subtype());
    const auto interface_method_id = ::interface_method_id(
      symbol_table,
      functional_interface_tag,
      method_identifier,
      instruction.address,
      log);
    if(!interface_method_id)
      continue;
    log.debug() << "identified invokedynamic at " << method_identifier
                << " address " << instruction.address
                << " for lambda: " << *lambda_method_name << messaget::eom;
    const irep_idt synthetic_class_name =
      lambda_synthetic_class_name(method_identifier, instruction.address);
    symbol_table.add(constructor_symbol(
      synthetic_methods, synthetic_class_name, dynamic_method_type));
    symbol_table.add(implemented_method_symbol(
      synthetic_methods,
      symbol_table.lookup_ref(*interface_method_id),
      functional_interface_tag,
      synthetic_class_name));
    symbol_table.add(synthetic_class_symbol(
      synthetic_class_name,
      *lambda_method_name,
      functional_interface_tag,
      dynamic_method_type));
  }
}

static const symbolt &get_or_create_method_symbol(
  const irep_idt &identifier,
  const irep_idt &base_name,
  const irep_idt &pretty_name,
  const typet &type,
  const irep_idt &declaring_class,
  symbol_table_baset &symbol_table,
  message_handlert &log)
{
  const auto *existing_symbol = symbol_table.lookup(identifier);
  if(existing_symbol)
    return *existing_symbol;

  create_method_stub_symbol(
    identifier,
    base_name,
    pretty_name,
    type,
    declaring_class,
    symbol_table,
    log);
  return symbol_table.lookup_ref(identifier);
}

codet invokedynamic_synthetic_constructor(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  code_blockt result;
  namespacet ns(symbol_table);

  const symbolt &function_symbol = ns.lookup(function_id);
  const auto &parameters = to_code_type(function_symbol.type).parameters();

  const symbolt &class_symbol = ns.lookup(*declaring_class(function_symbol));
  const class_typet &class_type = to_class_type(class_symbol.type);

  const symbol_exprt this_param(
    parameters.at(0).get_identifier(), parameters.at(0).type());
  const dereference_exprt deref_this(this_param);

  // Call super-constructor (always java.lang.Object):
  const irep_idt jlo("java::java.lang.Object");
  const irep_idt jlo_constructor(id2string(jlo) + ".<init>:()V");
  const auto jlo_reference = java_reference_type(struct_tag_typet(jlo));
  code_typet::parametert jlo_this_param{jlo_reference};
  jlo_this_param.set_this();

  java_method_typet jlo_constructor_type(
    code_typet::parameterst{jlo_this_param}, empty_typet());
  const auto &jlo_constructor_symbol = get_or_create_method_symbol(
    jlo_constructor,
    "<init>",
    jlo_constructor,
    jlo_constructor_type,
    jlo,
    symbol_table,
    message_handler);
  code_function_callt super_constructor_call(
    jlo_constructor_symbol.symbol_expr(),
    code_function_callt::argumentst{typecast_exprt(this_param, jlo_reference)});
  result.add(super_constructor_call);

  // Store captured parameters:
  auto field_iterator = std::next(class_type.components().begin());
  for(const auto &parameter : parameters)
  {
    // Give the parameter its symbol:
    parameter_symbolt param_symbol;
    param_symbol.name = parameter.get_identifier();
    param_symbol.base_name = parameter.get_base_name();
    param_symbol.mode = ID_java;
    param_symbol.type = parameter.type();
    symbol_table.add(param_symbol);

    if(parameter.get_this())
      continue;

    code_assignt assign_field(
      member_exprt(deref_this, field_iterator->get_name(), parameter.type()),
      symbol_exprt(parameter.get_identifier(), parameter.type()));
    result.add(assign_field);

    ++field_iterator;
  }

  return std::move(result);
}

codet invokedynamic_synthetic_method(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  // Call the bound method with the capture parameters, then the actual
  // parameters. Note one of the capture params might be the `this` parameter
  // of a virtual call -- that depends on whether the callee is a static or an
  // instance method.

  code_blockt result;
  namespacet ns(symbol_table);

  const symbolt &function_symbol = ns.lookup(function_id);
  const auto &function_type = to_code_type(function_symbol.type);
  const auto &parameters = function_type.parameters();
  const auto &return_type = function_type.return_type();

  const symbolt &class_symbol = ns.lookup(*declaring_class(function_symbol));
  const java_class_typet &class_type = to_java_class_type(class_symbol.type);

  const symbol_exprt this_param(
    parameters.at(0).get_identifier(), parameters.at(0).type());
  const dereference_exprt deref_this(this_param);

  code_function_callt::argumentst lambda_method_args;
  for(const auto &field : class_type.components())
  {
    if(field.get_name() == "@java.lang.Object")
      continue;
    lambda_method_args.push_back(
      member_exprt(deref_this, field.get_name(), field.type()));
  }

  for(const auto &parameter : parameters)
  {
    // Give the parameter its symbol:
    parameter_symbolt param_symbol;
    param_symbol.name = parameter.get_identifier();
    param_symbol.base_name = parameter.get_base_name();
    param_symbol.mode = ID_java;
    param_symbol.type = parameter.type();
    symbol_table.add(param_symbol);

    if(parameter.get_this())
      continue;

    lambda_method_args.push_back(param_symbol.symbol_expr());
  }

  const auto &lambda_method_symbol =
    ns.lookup(class_type.get(ID_java_lambda_method_identifier));

  if(return_type != empty_typet())
  {
    result.add(code_returnt(side_effect_expr_function_callt(
      lambda_method_symbol.symbol_expr(),
      lambda_method_args,
      return_type,
      source_locationt())));
  }
  else
  {
    result.add(code_function_callt(
      lambda_method_symbol.symbol_expr(), lambda_method_args));
  }

  return std::move(result);
}

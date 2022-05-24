/*******************************************************************\

Module: Java lambda code synthesis

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Java lambda code synthesis

#include "lambda_synthesis.h"

#include "jar_file.h"
#include "java_bytecode_convert_method.h"
#include "java_bytecode_parse_tree.h"
#include "java_static_initializers.h"
#include "java_types.h"
#include "java_utils.h"
#include "synthetic_methods_map.h"

#include <util/message.h>
#include <util/namespace.h>
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
static optionalt<java_class_typet::java_lambda_method_handlet>
get_lambda_method_handle(
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
  const auto &lambda_method_handle = lambda_method_handles.at(index);
  // If the lambda method handle has an unknown type, it does not refer to
  // any symbol (it has an empty identifier)
  if(
    lambda_method_handle.get_handle_kind() !=
    java_class_typet::method_handle_kindt::UNKNOWN_HANDLE)
    return lambda_method_handle;
  return {};
}

static optionalt<java_class_typet::java_lambda_method_handlet>
lambda_method_handle(
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
  return get_lambda_method_handle(
    symbol_table, lambda_method_handles, lambda_handle_index);
}

class no_unique_unimplemented_method_exceptiont : public std::exception
{
public:
  explicit no_unique_unimplemented_method_exceptiont(const std::string &s)
    : message(s)
  {
  }
  const std::string message;
};

struct compare_base_name_and_descriptort
{
  int operator()(
    const java_class_typet::methodt *a,
    const java_class_typet::methodt *b) const
  {
    return a->get_base_name() == b->get_base_name()
             ? (a->get_descriptor() == b->get_descriptor()
                  ? 0
                  : a->get_descriptor() < b->get_descriptor())
             : a->get_base_name() < b->get_base_name();
  }
};

/// Map from method, indexed by name and descriptor but not defining class, onto
/// defined-ness (i.e. true if defined with a default method, false if abstract)
typedef std::map<
  const java_class_typet::methodt *,
  bool,
  compare_base_name_and_descriptort>
  methods_by_name_and_descriptort;

/// Find all methods defined by this method and its parent types, returned as
/// a map from const java_class_typet::methodt * onto a boolean value which is
/// true if the method is defined (i.e. has a default definition) as of this
/// node in the class graph.
/// If there are multiple name-and-descriptor-compatible methods,
/// for example because both If1.f(int) and If2.f(int) are inherited here, only
/// one is stored in the map, chosen arbitrarily.
static const methods_by_name_and_descriptort
get_interface_methods(const irep_idt &interface_id, const namespacet &ns)
{
  static const irep_idt jlo = "java::java.lang.Object";
  // Terminate recursion at Object; any other base of an interface must
  // itself be an interface.
  if(jlo == interface_id)
    return {};

  const java_class_typet &interface =
    to_java_class_type(ns.lookup(interface_id).type);

  if(interface.get_is_stub())
  {
    throw no_unique_unimplemented_method_exceptiont(
      "produces a type that inherits the stub type " + id2string(interface_id));
  }

  methods_by_name_and_descriptort all_methods;

  // First accumulate definitions from child types:
  for(const auto &base : interface.bases())
  {
    const methods_by_name_and_descriptort base_methods =
      get_interface_methods(base.type().get_identifier(), ns);
    for(const auto &base_method : base_methods)
    {
      if(base_method.second)
      {
        // Any base definition fills any abstract definition from another base:
        all_methods[base_method.first] = true;
      }
      else
      {
        // An abstract method incoming from a base falls to any existing
        // definition, so only insert if not present:
        all_methods.emplace(base_method.first, false);
      }
    }
  }

  // Now insert defintions from this class:
  for(const auto &method : interface.methods())
  {
    static const irep_idt equals = "equals";
    static const irep_idt equals_descriptor = "(Ljava/lang/Object;)Z";
    static const irep_idt hashCode = "hashCode";
    static const irep_idt hashCode_descriptor = "()I";
    if(
      (method.get_base_name() == equals &&
       method.get_descriptor() == equals_descriptor) ||
      (method.get_base_name() == hashCode &&
       method.get_descriptor() == hashCode_descriptor))
    {
      // Ignore any uses of functions that are certainly defined on
      // java.lang.Object-- even if explicitly made abstract, they can't be the
      // implemented method of a functional interface.
      continue;
    }

    // Note unlike inherited definitions, an abstract definition here *does*
    // wipe out a non-abstract definition (i.e. a default method) from a parent
    // type.
    all_methods[&method] =
      !ns.lookup(method.get_name()).type.get_bool(ID_C_abstract);
  }

  return all_methods;
}

static const java_class_typet::methodt *try_get_unique_unimplemented_method(
  const symbol_tablet &symbol_table,
  const struct_tag_typet &functional_interface_tag,
  const irep_idt &method_identifier,
  const int instruction_address,
  const messaget &log)
{
  const namespacet ns{symbol_table};
  try
  {
    const methods_by_name_and_descriptort all_methods =
      get_interface_methods(functional_interface_tag.get_identifier(), ns);

    const java_class_typet::methodt *method_and_descriptor_to_implement =
      nullptr;

    for(const auto &entry : all_methods)
    {
      if(!entry.second)
      {
        if(method_and_descriptor_to_implement != nullptr)
        {
          throw no_unique_unimplemented_method_exceptiont(
            "produces a type with at least two unimplemented methods");
        }
        method_and_descriptor_to_implement = entry.first;
      }
    }

    if(!method_and_descriptor_to_implement)
    {
      throw no_unique_unimplemented_method_exceptiont(
        "produces a type with no unimplemented methods");
    }
    return method_and_descriptor_to_implement;
  }
  catch(const no_unique_unimplemented_method_exceptiont &e)
  {
    log.debug() << "ignoring invokedynamic at " << method_identifier
                << " address " << instruction_address << " with type "
                << functional_interface_tag.get_identifier() << " which "
                << e.message << "." << messaget::eom;
    return {};
  }
}

symbolt synthetic_class_symbol(
  const irep_idt &synthetic_class_name,
  const java_class_typet::java_lambda_method_handlet &lambda_method_handle,
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
  synthetic_class_type.set(ID_java_lambda_method_handle, lambda_method_handle);
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

  java_method_typet::parametert constructor_this_param(
    java_reference_type(struct_tag_typet(synthetic_class_name)));
  constructor_this_param.set_this();
  constructor_this_param.set_base_name("this");
  constructor_this_param.set_identifier(id2string(constructor_name) + "::this");

  constructor_type.parameters().insert(
    constructor_type.parameters().begin(), constructor_this_param);

  constructor_symbol.type = constructor_type;
  set_declaring_class(constructor_symbol, synthetic_class_name);
  return constructor_symbol;
}

static symbolt implemented_method_symbol(
  synthetic_methods_mapt &synthetic_methods,
  const java_class_typet::methodt &method_to_implement,
  const irep_idt &synthetic_class_name)
{
  const std::string implemented_method_name =
    id2string(synthetic_class_name) + "." +
    id2string(method_to_implement.get_base_name()) + ":" +
    id2string(method_to_implement.get_descriptor());

  symbolt implemented_method_symbol;
  implemented_method_symbol.name = implemented_method_name;
  synthetic_methods[implemented_method_symbol.name] =
    synthetic_method_typet::INVOKEDYNAMIC_METHOD;
  implemented_method_symbol.pretty_name = implemented_method_symbol.name;
  implemented_method_symbol.base_name = method_to_implement.get_base_name();
  implemented_method_symbol.mode = ID_java;
  implemented_method_symbol.type = method_to_implement.type();
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
    const auto lambda_handle = lambda_method_handle(
      symbol_table, method_identifier, dynamic_method_type);
    if(!lambda_handle)
    {
      log.debug() << "ignoring invokedynamic at " << method_identifier
                  << " address " << instruction.address
                  << " with unknown handle type" << messaget::eom;
      continue;
    }
    const auto &functional_interface_tag = to_struct_tag_type(
      to_java_reference_type(dynamic_method_type.return_type()).subtype());
    const auto unimplemented_method = try_get_unique_unimplemented_method(
      symbol_table,
      functional_interface_tag,
      method_identifier,
      instruction.address,
      log);
    if(!unimplemented_method)
      continue;
    log.debug() << "identified invokedynamic at " << method_identifier
                << " address " << instruction.address << " for lambda: "
                << lambda_handle->get_lambda_method_identifier()
                << messaget::eom;
    const irep_idt synthetic_class_name =
      lambda_synthetic_class_name(method_identifier, instruction.address);
    symbol_table.add(constructor_symbol(
      synthetic_methods, synthetic_class_name, dynamic_method_type));
    symbol_table.add(implemented_method_symbol(
      synthetic_methods, *unimplemented_method, synthetic_class_name));
    symbol_table.add(synthetic_class_symbol(
      synthetic_class_name,
      *lambda_handle,
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

    code_frontend_assignt assign_field(
      member_exprt(deref_this, field_iterator->get_name(), parameter.type()),
      symbol_exprt(parameter.get_identifier(), parameter.type()));
    result.add(assign_field);

    ++field_iterator;
  }

  return std::move(result);
}

static symbol_exprt create_and_declare_local(
  const irep_idt &function_id,
  const irep_idt &basename,
  const typet &type,
  symbol_table_baset &symbol_table,
  code_blockt &method)
{
  irep_idt new_var_name = id2string(function_id) + "::" + id2string(basename);
  auxiliary_symbolt new_instance_var_symbol;
  new_instance_var_symbol.name = new_var_name;
  new_instance_var_symbol.base_name = basename;
  new_instance_var_symbol.mode = ID_java;
  new_instance_var_symbol.type = type;
  bool add_failed = symbol_table.add(new_instance_var_symbol);
  POSTCONDITION(!add_failed);
  symbol_exprt new_instance_var = new_instance_var_symbol.symbol_expr();
  method.add(code_declt{new_instance_var});

  return new_instance_var;
}

/// Instantiates an object suitable for calling a given constructor (but does
/// not actually call it). Adds a local to symbol_table, and code implementing
/// the required operation to result; returns a symbol carrying a reference to
/// the newly instantiated object.
/// \param function_id: ID of the function that `result` falls within
/// \param lambda_method_symbol: the constructor that will be called, and so
///   whose `this` parameter we should instantiate.
/// \param symbol_table: symbol table, will gain a local variable
/// \param result: will gain instructions instantiating the required type
/// \return the newly instantiated symbol
static symbol_exprt instantiate_new_object(
  const irep_idt &function_id,
  const symbolt &lambda_method_symbol,
  symbol_table_baset &symbol_table,
  code_blockt &result)
{
  // We must instantiate the object, then call the requested constructor
  const auto &method_type = to_code_type(lambda_method_symbol.type);
  INVARIANT(
    method_type.get_bool(ID_constructor),
    "REF_NewInvokeSpecial lambda must refer to a constructor");
  const auto &created_type = method_type.parameters().at(0).type();
  irep_idt created_class =
    to_struct_tag_type(to_reference_type(created_type).base_type())
      .get_identifier();

  // Call static init if it exists:
  irep_idt static_init_name = clinit_wrapper_name(created_class);
  if(const auto *static_init_symbol = symbol_table.lookup(static_init_name))
  {
    result.add(code_function_callt{static_init_symbol->symbol_expr(), {}});
  }

  // Make a local to hold the new instance:
  symbol_exprt new_instance_var = create_and_declare_local(
    function_id,
    "newinvokespecial_instance",
    created_type,
    symbol_table,
    result);

  // Instantiate the object:
  side_effect_exprt java_new_expr(ID_java_new, created_type, {});
  result.add(code_frontend_assignt{new_instance_var, java_new_expr});

  return new_instance_var;
}

/// If \p maybe_boxed_type is a boxed primitive return its unboxing method;
/// otherwise return empty.
static optionalt<irep_idt>
get_unboxing_method(const pointer_typet &maybe_boxed_type)
{
  const irep_idt &boxed_type_id =
    to_struct_tag_type(maybe_boxed_type.base_type()).get_identifier();
  const java_boxed_type_infot *boxed_type_info =
    get_boxed_type_info_by_name(boxed_type_id);
  return boxed_type_info ? boxed_type_info->unboxing_function_name
                         : optionalt<irep_idt>{};
}

/// Produce a class_method_descriptor_exprt or symbol_exprt for
/// \p function_symbol depending on whether virtual dispatch could be required
/// (i.e., if it is non-static and its 'this' parameter is a non-final type)
exprt make_function_expr(
  const symbolt &function_symbol,
  const symbol_tablet &symbol_table)
{
  const auto &method_type = to_java_method_type(function_symbol.type);
  if(!method_type.has_this())
    return function_symbol.symbol_expr();
  const irep_idt &declared_on_class_id =
    to_struct_tag_type(
      to_pointer_type(method_type.get_this()->type()).base_type())
      .get_identifier();
  const auto &this_symbol = symbol_table.lookup_ref(declared_on_class_id);
  if(to_java_class_type(this_symbol.type).get_final())
    return function_symbol.symbol_expr();

  // Neither final nor static; make a class_method_descriptor_exprt that will
  // trigger remove_virtual_functions to produce a virtual dispatch table:

  const std::string &function_name = id2string(function_symbol.name);
  const auto method_name_start_idx = function_name.rfind('.');
  const irep_idt mangled_method_name =
    function_name.substr(method_name_start_idx + 1);

  return class_method_descriptor_exprt{function_symbol.type,
                                       mangled_method_name,
                                       declared_on_class_id,
                                       function_symbol.base_name};
}

/// If \p expr needs (un)boxing to satisfy \p required_type, add the required
/// symbols to \p symbol_table and code to \p code_block, then return an
/// expression giving the adjusted expression. Otherwise return \p expr
/// unchanged. \p role is a suggested name prefix for any temporary variable
/// needed; \p function_id is the id of the function any created code it
/// added to.
///
/// Regarding the apparent behaviour of the Java compiler / runtime with regard
/// to adapting generic methods to/from primtitive types:
///
/// When unboxing, it appears to permit widening numeric conversions at the
/// same time. For example, implementing Consumer<Short> by a function of
/// type long -> void is possible, as the generated function will look like
/// impl(Object o) { realfunc(((Number)o).longValue()); }
///
/// On the other hand when boxing to satisfy a generic interface type this is
/// not permitted: in theory we should be able to implement Producer<Long> by a
/// function of type () -> int, generating boxing code like
/// impl() { return Long.valueOf(realfunc()); }
///
/// However it appears there is no way to convey to the lambda metafactory
/// that a Long is really required rather than an Integer (the obvious
/// conversion from int), so the compiler forbids this and requires that only
/// simple boxing is performed.
///
/// Therefore when unboxing we cast to Number first, while when boxing and the
/// target type is not a specific boxed type (i.e. the target is Object or
/// Number etc) then we use the primitive type as our cue regarding the boxed
/// type to produce.
exprt box_or_unbox_type_if_necessary(
  exprt expr,
  const typet &required_type,
  code_blockt &code_block,
  symbol_table_baset &symbol_table,
  const irep_idt &function_id,
  const std::string &role)
{
  const typet &original_type = expr.type();
  const bool original_is_pointer = can_cast_type<pointer_typet>(original_type);
  const bool required_is_pointer = can_cast_type<pointer_typet>(required_type);

  if(original_is_pointer == required_is_pointer)
  {
    return expr;
  }

  // One is a pointer, the other a primitive -- box or unbox as necessary, and
  // check the types are consistent:

  const auto *primitive_type_info = get_java_primitive_type_info(
    original_is_pointer ? required_type : original_type);
  INVARIANT(
    primitive_type_info != nullptr,
    "A Java non-pointer type involved in a type disagreement should"
    " be a primitive");

  const irep_idt fresh_local_name =
    role + (original_is_pointer ? "_unboxed" : "_boxed");

  const symbol_exprt fresh_local = create_and_declare_local(
    function_id, fresh_local_name, required_type, symbol_table, code_block);

  const irep_idt transform_function_id =
    original_is_pointer
      ? get_unboxing_method(
          to_pointer_type(original_type)) // Use static type if known
          .value_or(primitive_type_info->unboxing_function_name)
      : primitive_type_info->boxed_type_factory_method;

  const symbolt &transform_function_symbol =
    symbol_table.lookup_ref(transform_function_id);

  const typet &transform_function_param_type =
    to_code_type(transform_function_symbol.type).parameters()[0].type();
  const exprt cast_expr =
    typecast_exprt::conditional_cast(expr, transform_function_param_type);

  code_block.add(code_function_callt{
    fresh_local,
    make_function_expr(transform_function_symbol, symbol_table),
    {expr}});

  return std::move(fresh_local);
}

/// Box or unbox expr as per \ref box_or_unbox_type_if_necessary, then cast the
/// result to \p required_type. If the source is legal Java that should mean a
/// pointer upcast or primitive widening conversion, but this is not checked.
exprt adjust_type_if_necessary(
  exprt expr,
  const typet &required_type,
  code_blockt &code_block,
  symbol_table_baset &symbol_table,
  const irep_idt &function_id,
  const std::string &role)
{
  return typecast_exprt::conditional_cast(
    box_or_unbox_type_if_necessary(
      expr, required_type, code_block, symbol_table, function_id, role),
    required_type);
}

/// Create the body for the synthetic method implementing an invokedynamic
/// method. For most lambdas this means creating a simple function body like
/// TR new_synthetic_method(T1 param1, T2 param2, ...) {
///   return target_method(capture1, capture2, ..., param1, param2, ...);
/// }, where the first parameter might be a `this` parameter.
/// For a constructor method, the generated code will be of the form
/// TNew new_synthetic_method(T1 param1, T2 param2, ...) {
///   return new TNew(capture1, capture2, ..., param1, param2, ...);
/// }
/// i.e. the TNew object will be both instantiated and constructed.
/// \param function_id: synthetic method whose body should be generated;
///   information about the lambda method to generate has already been stored
///   in the symbol table by create_invokedynamic_synthetic_classes.
/// \param symbol_table: will gain local variable symbols
/// \param message_handler: log
/// \return the method body for `function_id`
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

  const auto &lambda_method_handle =
    static_cast<const java_class_typet::java_lambda_method_handlet &>(
      class_type.find(ID_java_lambda_method_handle));

  const auto &lambda_method_symbol =
    ns.lookup(lambda_method_handle.get_lambda_method_identifier());
  const auto handle_type = lambda_method_handle.get_handle_kind();
  const auto is_constructor_lambda =
    handle_type ==
    java_class_typet::method_handle_kindt::LAMBDA_CONSTRUCTOR_HANDLE;
  const auto use_virtual_dispatch =
    handle_type ==
    java_class_typet::method_handle_kindt::LAMBDA_VIRTUAL_METHOD_HANDLE;

  if(is_constructor_lambda)
  {
    auto new_instance_var = instantiate_new_object(
      function_id, lambda_method_symbol, symbol_table, result);

    // Prepend the newly created object to the lambda arg list:
    lambda_method_args.insert(lambda_method_args.begin(), new_instance_var);
  }

  const auto &lambda_method_descriptor =
    lambda_method_handle.get_lambda_method_descriptor();
  exprt callee;
  if(use_virtual_dispatch)
    callee = lambda_method_descriptor;
  else
    callee = lambda_method_symbol.symbol_expr();

  // Adjust boxing if required:
  const code_typet &callee_type = to_code_type(lambda_method_symbol.type);
  const auto &callee_parameters = callee_type.parameters();
  const auto &callee_return_type = callee_type.return_type();
  INVARIANT(
    callee_parameters.size() == lambda_method_args.size(),
    "should have args for every parameter");
  for(unsigned i = 0; i < callee_parameters.size(); ++i)
  {
    lambda_method_args[i] = adjust_type_if_necessary(
      std::move(lambda_method_args[i]),
      callee_parameters[i].type(),
      result,
      symbol_table,
      function_id,
      "param" + std::to_string(i));
  }

  if(function_type.return_type() != empty_typet() && !is_constructor_lambda)
  {
    symbol_exprt result_local = create_and_declare_local(
      function_id, "return_value", callee_return_type, symbol_table, result);
    result.add(code_function_callt(result_local, callee, lambda_method_args));
    exprt adjusted_local = adjust_type_if_necessary(
      result_local,
      function_type.return_type(),
      result,
      symbol_table,
      function_id,
      "retval");
    result.add(code_returnt{adjusted_local});
  }
  else
  {
    result.add(code_function_callt(callee, lambda_method_args));
  }

  if(is_constructor_lambda)
  {
    // Return the newly-created object.
    result.add(code_returnt{typecast_exprt::conditional_cast(
      lambda_method_args.at(0), function_type.return_type())});
  }

  return std::move(result);
}

/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Language Conversion

#ifdef DEBUG
#include <iostream>
#endif

#include "bytecode_info.h"
#include "java_bytecode_convert_method.h"
#include "java_bytecode_convert_method_class.h"
#include "java_expr.h"
#include "java_static_initializers.h"
#include "java_string_library_preprocess.h"
#include "java_string_literal_expr.h"
#include "java_types.h"
#include "java_utils.h"
#include "lambda_synthesis.h"
#include "pattern.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/floatbv_expr.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/prefix_filter.h>
#include <util/std_expr.h>
#include <util/threeval.h>

#include <goto-programs/resolve_inherited_component.h>

#include <analyses/uncaught_exceptions_analysis.h>

#include <algorithm>
#include <limits>

/// Iterates through the parameters of the function type \p ftype, finds a new
/// new name for each parameter and renames them in `ftype.parameters()` as
/// well as in the \p symbol_table.
/// \param [in,out] ftype:
///   Function type whose parameters should be named.
/// \param name_prefix:
///   Prefix for parameter names, typically the parent function's name.
/// \param [in,out] symbol_table:
///   Global symbol table.
/// \return Assigns parameter names (side-effects on `ftype`) to function stub
///   parameters, which are initially nameless as method conversion hasn't
///   happened. Also creates symbols in `symbol_table`.
static void assign_parameter_names(
  java_method_typet &ftype,
  const irep_idt &name_prefix,
  symbol_table_baset &symbol_table)
{
  java_method_typet::parameterst &parameters = ftype.parameters();

  // Mostly borrowed from java_bytecode_convert.cpp; maybe factor this out.
  // assign names to parameters
  for(std::size_t i=0; i<parameters.size(); ++i)
  {
    irep_idt base_name, identifier;

    if(i==0 && parameters[i].get_this())
      base_name = ID_this;
    else
      base_name="stub_ignored_arg"+std::to_string(i);

    identifier=id2string(name_prefix)+"::"+id2string(base_name);
    parameters[i].set_base_name(base_name);
    parameters[i].set_identifier(identifier);

    // add to symbol table
    parameter_symbolt parameter_symbol;
    parameter_symbol.base_name=base_name;
    parameter_symbol.mode=ID_java;
    parameter_symbol.name=identifier;
    parameter_symbol.type=parameters[i].type();
    symbol_table.add(parameter_symbol);
  }
}

void create_method_stub_symbol(
  const irep_idt &identifier,
  const irep_idt &base_name,
  const irep_idt &pretty_name,
  const typet &type,
  const irep_idt &declaring_class,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  messaget log(message_handler);

  symbolt symbol;
  symbol.name = identifier;
  symbol.base_name = base_name;
  symbol.pretty_name = pretty_name;
  symbol.type = type;
  symbol.type.set(ID_access, ID_private);
  to_java_method_type(symbol.type).set_is_final(true);
  symbol.value.make_nil();
  symbol.mode = ID_java;
  assign_parameter_names(
    to_java_method_type(symbol.type), symbol.name, symbol_table);
  set_declaring_class(symbol, declaring_class);

  log.debug() << "Generating codet:  new opaque symbol: method '" << symbol.name
              << "'" << messaget::eom;
  symbol_table.add(symbol);
}

static bool is_constructor(const irep_idt &method_name)
{
  return id2string(method_name).find("<init>") != std::string::npos;
}

exprt::operandst java_bytecode_convert_methodt::pop(std::size_t n)
{
  if(stack.size()<n)
  {
    log.error() << "malformed bytecode (pop too high)" << messaget::eom;
    throw 0;
  }

  exprt::operandst operands;
  operands.resize(n);
  for(std::size_t i=0; i<n; i++)
    operands[i]=stack[stack.size()-n+i];

  stack.resize(stack.size()-n);
  return operands;
}

/// removes minimum(n, stack.size()) elements from the stack
void java_bytecode_convert_methodt::pop_residue(std::size_t n)
{
  std::size_t residue_size=std::min(n, stack.size());

  stack.resize(stack.size()-residue_size);
}

void java_bytecode_convert_methodt::push(const exprt::operandst &o)
{
  stack.resize(stack.size()+o.size());

  for(std::size_t i=0; i<o.size(); i++)
    stack[stack.size()-o.size()+i]=o[i];
}

// JVM program locations
irep_idt java_bytecode_convert_methodt::label(const irep_idt &address)
{
  return "pc"+id2string(address);
}

symbol_exprt java_bytecode_convert_methodt::tmp_variable(
  const std::string &prefix,
  const typet &type)
{
  irep_idt base_name=prefix+"_tmp"+std::to_string(tmp_vars.size());
  irep_idt identifier=id2string(current_method)+"::"+id2string(base_name);

  auxiliary_symbolt tmp_symbol;
  tmp_symbol.base_name=base_name;
  tmp_symbol.is_static_lifetime=false;
  tmp_symbol.mode=ID_java;
  tmp_symbol.name=identifier;
  tmp_symbol.type=type;
  symbol_table.add(tmp_symbol);

  symbol_exprt result(identifier, type);
  result.set(ID_C_base_name, base_name);
  tmp_vars.push_back(result);

  return result;
}

/// Returns an expression indicating a local variable suitable to load/store
/// from a bytecode at address `address` a value of type `type_char` stored in
/// the JVM's slot `arg`.
/// \param arg: The local variable slot
/// \param type_char: The type of the value stored in the slot pointed to by
///   `arg`, this is only used in the case where a new unnamed local variable
///   is created
/// \param address: Bytecode address used to find a variable that the LVT
///   declares to be live and living in the slot pointed by `arg` for this
///   bytecode
/// \return symbol_exprt or type-cast symbol_exprt
exprt java_bytecode_convert_methodt::variable(
  const exprt &arg,
  char type_char,
  size_t address)
{
  const std::size_t number_int =
    numeric_cast_v<std::size_t>(to_constant_expr(arg));
  variablest &var_list=variables[number_int];

  // search variable in list for correct frame / address if necessary
  const variablet &var=
    find_variable_for_slot(address, var_list);

  if(!var.symbol_expr.get_identifier().empty())
    return var.symbol_expr;

  // an unnamed local variable
  irep_idt base_name = "anonlocal::" + std::to_string(number_int) + type_char;
  irep_idt identifier = id2string(current_method) + "::" + id2string(base_name);

  symbol_exprt result(identifier, java_type_from_char(type_char));
  result.set(ID_C_base_name, base_name);
  used_local_names.insert(result);
  return std::move(result);
}

/// Returns the member type for a method, based on signature or descriptor
/// \param descriptor: descriptor of the method
/// \param signature: signature of the method
/// \param class_name: string containing the name of the corresponding class
/// \param method_name: string containing the name of the method
/// \param message_handler: message handler to collect warnings
/// \return the constructed member type
java_method_typet member_type_lazy(
  const std::string &descriptor,
  const optionalt<std::string> &signature,
  const std::string &class_name,
  const std::string &method_name,
  message_handlert &message_handler)
{
  // In order to construct the method type, we can either use signature or
  // descriptor. Since only signature contains the generics info, we want to
  // use signature whenever possible. We revert to using descriptor if (1) the
  // signature does not exist, (2) an unsupported generics are present or
  // (3) in the special case when the number of parameters in the descriptor
  // does not match the number of parameters in the signature - e.g. for
  // certain types of inner classes and enums (see unit tests for examples).

  messaget message(message_handler);

  auto member_type_from_descriptor = java_type_from_string(descriptor);
  INVARIANT(
    member_type_from_descriptor.has_value() &&
      member_type_from_descriptor->id() == ID_code,
    "Must be code type");
  if(signature.has_value())
  {
    try
    {
      auto member_type_from_signature =
        java_type_from_string(signature.value(), class_name);
      INVARIANT(
        member_type_from_signature.has_value() &&
          member_type_from_signature->id() == ID_code,
        "Must be code type");
      if(
        to_java_method_type(*member_type_from_signature).parameters().size() ==
        to_java_method_type(*member_type_from_descriptor).parameters().size())
      {
        return to_java_method_type(*member_type_from_signature);
      }
      else
      {
        message.debug() << "Method: " << class_name << "." << method_name
                        << "\n signature: " << signature.value()
                        << "\n descriptor: " << descriptor
                        << "\n different number of parameters, reverting to "
                           "descriptor"
                        << message.eom;
      }
    }
    catch(const unsupported_java_class_signature_exceptiont &e)
    {
      message.debug() << "Method: " << class_name << "." << method_name
                      << "\n could not parse signature: " << signature.value()
                      << "\n " << e.what() << "\n"
                      << " reverting to descriptor: " << descriptor
                      << message.eom;
    }
  }
  return to_java_method_type(*member_type_from_descriptor);
}

/// This creates a method symbol in the symtab, but doesn't actually perform
/// method conversion just yet. The caller should call
/// java_bytecode_convert_method later to give the symbol/method a body.
/// \param class_symbol: The class this method belongs to. The method, if not
///   static, will be added to the class' list of methods.
/// \param method_identifier: The fully qualified method name, including type
///   descriptor (e.g. "x.y.z.f:(I)")
/// \param m: The parsed method object to convert.
/// \param symbol_table: The global symbol table (will be modified).
/// \param message_handler: A message handler to collect warnings.
void java_bytecode_convert_method_lazy(
  symbolt &class_symbol,
  const irep_idt &method_identifier,
  const java_bytecode_parse_treet::methodt &m,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  symbolt method_symbol;

  java_method_typet member_type = member_type_lazy(
    m.descriptor,
    m.signature,
    id2string(class_symbol.name),
    id2string(m.base_name),
    message_handler);

  method_symbol.name=method_identifier;
  method_symbol.base_name=m.base_name;
  method_symbol.mode=ID_java;
  method_symbol.location=m.source_location;
  method_symbol.location.set_function(method_identifier);

  if(m.is_public)
    member_type.set_access(ID_public);
  else if(m.is_protected)
    member_type.set_access(ID_protected);
  else if(m.is_private)
    member_type.set_access(ID_private);
  else
    member_type.set_access(ID_default);

  if(m.is_synchronized)
    member_type.set(ID_is_synchronized, true);
  if(m.is_static)
    member_type.set(ID_is_static, true);
  member_type.set_native(m.is_native);
  member_type.set_is_varargs(m.is_varargs);
  member_type.set_is_synthetic(m.is_synthetic);

  if(m.is_bridge)
    member_type.set(ID_is_bridge_method, m.is_bridge);

  // do we need to add 'this' as a parameter?
  if(!m.is_static)
  {
    java_method_typet::parameterst &parameters = member_type.parameters();
    const reference_typet object_ref_type =
      java_reference_type(struct_tag_typet(class_symbol.name));
    java_method_typet::parametert this_p(object_ref_type);
    this_p.set_this();
    parameters.insert(parameters.begin(), this_p);
  }

  const std::string signature_string = pretty_signature(member_type);

  if(is_constructor(method_symbol.base_name))
  {
    // we use full.class_name(...) as pretty name
    // for constructors -- the idea is that they have
    // an empty declarator.
    method_symbol.pretty_name=
      id2string(class_symbol.pretty_name) + signature_string;

    member_type.set_is_constructor();
  }
  else
  {
    method_symbol.pretty_name = id2string(class_symbol.pretty_name) + "." +
                                id2string(m.base_name) + signature_string;
  }

  // Load annotations
  if(!m.annotations.empty())
  {
    convert_annotations(
      m.annotations,
      type_checked_cast<annotated_typet>(static_cast<typet &>(member_type))
        .get_annotations());
  }

  method_symbol.type=member_type;
  // Not used in jbmc at present, but other codebases that use jbmc as a library
  // use this information.
  method_symbol.type.set(ID_C_abstract, m.is_abstract);
  set_declaring_class(method_symbol, class_symbol.name);

  if(java_bytecode_parse_treet::find_annotation(
       m.annotations, "java::org.cprover.MustNotThrow"))
  {
    method_symbol.type.set(ID_C_must_not_throw, true);
  }

  // Assign names to parameters in the method symbol
  java_method_typet &method_type = to_java_method_type(method_symbol.type);
  method_type.set_is_final(m.is_final);
  java_method_typet::parameterst &parameters = method_type.parameters();
  java_bytecode_convert_methodt::method_offsett slots_for_parameters =
    java_method_parameter_slots(method_type);
  create_parameter_names(
    m, method_identifier, parameters, slots_for_parameters);

  symbol_table.add(method_symbol);

  if(!m.is_static)
  {
    java_class_typet::methodt new_method{method_symbol.name, method_type};
    new_method.set_base_name(method_symbol.base_name);
    new_method.set_pretty_name(method_symbol.pretty_name);
    new_method.set_access(member_type.get_access());
    new_method.set_descriptor(m.descriptor);

    to_java_class_type(class_symbol.type)
      .methods()
      .emplace_back(std::move(new_method));
  }
}

static irep_idt get_method_identifier(
  const irep_idt &class_identifier,
  const java_bytecode_parse_treet::methodt &method)
{
  return
    id2string(class_identifier) + "." + id2string(method.name) + ":" +
    method.descriptor;
}

void create_parameter_names(
  const java_bytecode_parse_treet::methodt &m,
  const irep_idt &method_identifier,
  java_method_typet::parameterst &parameters,
  const java_bytecode_convert_methodt::method_offsett &slots_for_parameters)
{
  auto variables = variablest{};
  // Find parameter names in the local variable table
  // and store the result in the external variables vector
  for(const auto &v : m.local_variable_table)
  {
    // Skip this variable if it is not a method parameter
    if(v.index >= slots_for_parameters)
      continue;

    std::ostringstream id_oss;
    id_oss << method_identifier << "::" << v.name;
    irep_idt identifier(id_oss.str());
    symbol_exprt result = symbol_exprt::typeless(identifier);
    result.set(ID_C_base_name, v.name);

    // Create a new variablet in the variables vector; in fact this entry will
    // be rewritten below in the loop that iterates through the method
    // parameters; the only field that seem to be useful to write here is the
    // symbol_expr, others will be rewritten
    variables[v.index].emplace_back(result, v.start_pc, v.length);
  }

  // The variables is a expanding_vectort, and the loop above may have expanded
  // the vector introducing gaps where the entries are empty vectors. We now
  // make sure that the vector of each LV slot contains exactly one variablet,
  // which we will add below
  std::size_t param_index = 0;
  for(const auto &param : parameters)
  {
    INVARIANT(
      variables[param_index].size() <= 1,
      "should have at most one entry per index");
    param_index += java_local_variable_slots(param.type());
  }
  INVARIANT(
    param_index == slots_for_parameters,
    "java_parameter_count and local computation must agree");
  param_index = 0;
  for(auto &param : parameters)
  {
    irep_idt base_name, identifier;

    // Construct a sensible base name (base_name) and a fully qualified name
    // (identifier) for every parameter of the method under translation,
    // regardless of whether we have an LVT or not; and assign it to the
    // parameter object (which is stored in the type of the symbol, not in the
    // symbol table)
    if(param_index == 0 && param.get_this())
    {
      // my.package.ClassName.myMethodName:(II)I::this
      base_name = ID_this;
      identifier = id2string(method_identifier) + "::" + id2string(base_name);
    }
    else if(!variables[param_index].empty())
    {
      // if already present in the LVT ...
      base_name = variables[param_index][0].symbol_expr.get(ID_C_base_name);
      identifier = variables[param_index][0].symbol_expr.get(ID_identifier);
    }
    else
    {
      // my.package.ClassName.myMethodName:(II)I::argNT, where N is the local
      // variable slot where the parameter is stored and T is a character
      // indicating the type
      char suffix = java_char_from_type(param.type());
      base_name = "arg" + std::to_string(param_index) + suffix;
      identifier = id2string(method_identifier) + "::" + id2string(base_name);
    }
    param.set_base_name(base_name);
    param.set_identifier(identifier);
    param_index += java_local_variable_slots(param.type());
  }
  // The parameter slots detected in this function should agree with what
  // java_parameter_count() thinks about this method
  INVARIANT(
    param_index == slots_for_parameters,
    "java_parameter_count and local computation must agree");
}

void create_parameter_symbols(
  const java_method_typet::parameterst &parameters,
  expanding_vectort<std::vector<java_bytecode_convert_methodt::variablet>>
    &variables,
  symbol_table_baset &symbol_table)
{
  std::size_t param_index = 0;
  for(const auto &param : parameters)
  {
    parameter_symbolt parameter_symbol;
    parameter_symbol.base_name = param.get_base_name();
    parameter_symbol.mode = ID_java;
    parameter_symbol.name = param.get_identifier();
    parameter_symbol.type = param.type();
    symbol_table.add(parameter_symbol);

    // Add as a JVM local variable
    variables[param_index].clear();
    variables[param_index].emplace_back(
      parameter_symbol.symbol_expr(),
      0,
      std::numeric_limits<size_t>::max(),
      true);
    param_index += java_local_variable_slots(param.type());
  }
}

void java_bytecode_convert_methodt::convert(
  const symbolt &class_symbol,
  const methodt &m,
  const optionalt<prefix_filtert> &method_context)
{
  // Construct the fully qualified method name
  // (e.g. "my.package.ClassName.myMethodName:(II)I") and query the symbol table
  // to retrieve the symbol (constructed by java_bytecode_convert_method_lazy)
  // associated to the method
  const irep_idt method_identifier =
    get_method_identifier(class_symbol.name, m);

  method_id = method_identifier;
  set_declaring_class(
    symbol_table.get_writeable_ref(method_identifier), class_symbol.name);

  // Obtain a std::vector of java_method_typet::parametert objects from the
  // (function) type of the symbol
  // Don't try to hang on to this reference into the symbol table, as we're
  // about to create symbols for the method's parameters, which would invalidate
  // the reference. Instead, copy the type here, set it up, then assign it back
  // to the symbol later.
  java_method_typet method_type =
    to_java_method_type(symbol_table.lookup_ref(method_identifier).type);
  method_type.set_is_final(m.is_final);
  method_return_type = method_type.return_type();
  java_method_typet::parameterst &parameters = method_type.parameters();

  // Determine the number of local variable slots used by the JVM to maintain
  // the formal parameters
  slots_for_parameters = java_method_parameter_slots(method_type);

  log.debug() << "Generating codet: class " << class_symbol.name << ", method "
              << m.name << messaget::eom;

  // Add parameter symbols to the symbol table
  create_parameter_symbols(parameters, variables, symbol_table);

  symbolt &method_symbol = symbol_table.get_writeable_ref(method_identifier);

  // Check the fields that can't change are valid
  INVARIANT(
    method_symbol.name == method_identifier,
    "Name of method symbol shouldn't change");
  INVARIANT(
    method_symbol.base_name == m.base_name,
    "Base name of method symbol shouldn't change");
  INVARIANT(
    method_symbol.module.empty(),
    "Method symbol shouldn't have module");
  // Update the symbol for the method
  method_symbol.mode=ID_java;
  method_symbol.location=m.source_location;
  method_symbol.location.set_function(method_identifier);

  for(const auto &exception_name : m.throws_exception_table)
    method_type.add_throws_exception(exception_name);

  const std::string signature_string = pretty_signature(method_type);

  // Set up the pretty name for the method entry in the symbol table.
  // The pretty name of a constructor includes the base name of the class
  // instead of the internal method name "<init>". For regular methods, it's
  // just the base name of the method.
  if(is_constructor(method_symbol.base_name))
  {
    // we use full.class_name(...) as pretty name
    // for constructors -- the idea is that they have
    // an empty declarator.
    method_symbol.pretty_name =
      id2string(class_symbol.pretty_name) + signature_string;
    INVARIANT(
      method_type.get_is_constructor(),
      "Member type should have already been marked as a constructor");
  }
  else
  {
    method_symbol.pretty_name = id2string(class_symbol.pretty_name) + "." +
                                id2string(m.base_name) + signature_string;
  }

  method_symbol.type = method_type;
  current_method = method_symbol.name;
  method_has_this = method_type.has_this();
  if((!m.is_abstract) && (!m.is_native))
  {
    // Do not convert if method is not in context
    if(!method_context || (*method_context)(id2string(method_identifier)))
    {
      code_blockt code{convert_parameter_annotations(m, method_type)};
      code.append(convert_instructions(m));
      method_symbol.value = std::move(code);
    }
  }
}

static irep_idt get_if_cmp_operator(const u1 bytecode)
{
  if(bytecode == patternt("if_?cmplt"))
    return ID_lt;
  if(bytecode == patternt("if_?cmple"))
    return ID_le;
  if(bytecode == patternt("if_?cmpgt"))
    return ID_gt;
  if(bytecode == patternt("if_?cmpge"))
    return ID_ge;
  if(bytecode == patternt("if_?cmpeq"))
    return ID_equal;
  if(bytecode == patternt("if_?cmpne"))
    return ID_notequal;

  throw "unhandled java comparison instruction";
}

/// Build a member exprt for accessing a specific field that may come from a
/// base class.
/// \param pointer: The expression to access the field on.
/// \param field_reference: A getfield/setfield instruction produced by the
///   bytecode parser.
/// \param ns: Global namespace
/// \return A member expression accessing the field, through base class
///   components if necessary.
static member_exprt to_member(
  const exprt &pointer,
  const fieldref_exprt &field_reference,
  const namespacet &ns)
{
  struct_tag_typet class_type(field_reference.class_name());

  const exprt typed_pointer =
    typecast_exprt::conditional_cast(pointer, java_reference_type(class_type));

  const irep_idt &component_name = field_reference.component_name();

  exprt accessed_object = checked_dereference(typed_pointer);
  const auto type_of = [&ns](const exprt &object) {
    return to_struct_type(ns.follow(object.type()));
  };

  // The field access is described as being against a particular type, but it
  // may in fact belong to any ancestor type.
  while(type_of(accessed_object).get_component(component_name).is_nil())
  {
    const auto components = type_of(accessed_object).components();
    INVARIANT(
      components.size() != 0,
      "infer_opaque_type_fields should guarantee that a member access has a "
      "corresponding field");

    // Base class access is always done through the first component
    accessed_object = member_exprt(accessed_object, components.front());
  }
  return member_exprt(
    accessed_object, type_of(accessed_object).get_component(component_name));
}

/// Find all goto statements in 'repl' that target 'old_label' and redirect them
/// to 'new_label'.
/// \param [in,out] repl: A block of code in which to perform replacement.
/// \param old_label: The label to be replaced.
/// \param new_label: The label to replace `old_label` with.
void java_bytecode_convert_methodt::replace_goto_target(
  codet &repl,
  const irep_idt &old_label,
  const irep_idt &new_label)
{
  const auto &stmt=repl.get_statement();
  if(stmt==ID_goto)
  {
    auto &g=to_code_goto(repl);
    if(g.get_destination()==old_label)
      g.set_destination(new_label);
  }
  else
  {
    for(auto &op : repl.operands())
      if(op.id()==ID_code)
        replace_goto_target(to_code(op), old_label, new_label);
  }
}

/// 'tree' describes a tree of code_blockt objects; this_block is the
/// corresponding block (thus they are both trees with the same shape). The
/// caller is looking for the single block in the tree that most closely
/// encloses bytecode address range [address_start,address_limit).
/// 'next_block_start_address' is the start address of 'tree's successor sibling
/// and is used to determine when the range spans out of its bounds.
/// \param tree: A code block descriptor.
/// \param this_block: The corresponding actual \ref code_blockt.
/// \param address_start: the Java bytecode offsets searched for.
/// \param address_limit: the Java bytecode offsets searched for.
/// \param next_block_start_address: The bytecode offset of tree/this_block's
///   successor sibling, or UINT_MAX if none exists.
/// \return Returns the code_blockt most closely enclosing the given address
///   range.
code_blockt &java_bytecode_convert_methodt::get_block_for_pcrange(
  block_tree_nodet &tree,
  code_blockt &this_block,
  method_offsett address_start,
  method_offsett address_limit,
  method_offsett next_block_start_address)
{
  address_mapt dummy;
  return get_or_create_block_for_pcrange(
    tree,
    this_block,
    address_start,
    address_limit,
    next_block_start_address,
    dummy,
    false);
}

/// As above, but this version can additionally create a new branch in the
/// block_tree-node and code_blockt trees to envelop the requested address
/// range. For example, if the tree was initially flat, with nodes (1-10),
/// (11-20), (21-30) and the caller asked for range 13-28, this would build a
/// surrounding tree node, leaving the tree of shape (1-10), ^( (11-20), (21-30)
/// )^, and return a reference to the new branch highlighted with ^^. 'tree' and
/// 'this_block' trees are always maintained with equal shapes. ('this_block'
/// may additionally contain code_declt children which are ignored for this
/// purpose).
/// \param [in, out] tree: A code block descriptor.
/// \param [in,out] this_block: The corresponding actual \ref code_blockt.
/// \param address_start: the Java bytecode offsets searched for.
/// \param address_limit: the Java bytecode offsets searched for.
/// \param next_block_start_address: The bytecode offset of tree/this_block's
///   successor sibling, or UINT_MAX if none exists.
/// \param amap: The bytecode address map.
/// \param allow_merge: Whether modifying the block tree is allowed. This is
///   always true except when called from `get_block_for_pcrange`.
/// \return The code_blockt most closely enclosing the given address range.
code_blockt &java_bytecode_convert_methodt::get_or_create_block_for_pcrange(
  block_tree_nodet &tree,
  code_blockt &this_block,
  method_offsett address_start,
  method_offsett address_limit,
  method_offsett next_block_start_address,
  const address_mapt &amap,
  bool allow_merge)
{
  // Check the tree shape invariant:
  assert(tree.branch.size()==tree.branch_addresses.size());

  // If there are no child blocks, return this.
  if(tree.leaf)
    return this_block;
  assert(!tree.branch.empty());

  // Find child block starting > address_start:
  const auto afterstart=
    std::upper_bound(
      tree.branch_addresses.begin(),
      tree.branch_addresses.end(),
      address_start);
  assert(afterstart!=tree.branch_addresses.begin());
  auto findstart=afterstart;
  --findstart;
  auto child_offset=
    std::distance(tree.branch_addresses.begin(), findstart);

  // Find child block starting >= address_limit:
  auto findlim=
    std::lower_bound(
      tree.branch_addresses.begin(),
      tree.branch_addresses.end(),
      address_limit);
  const auto findlim_block_start_address =
    findlim == tree.branch_addresses.end() ? next_block_start_address
                                           : (*findlim);

  // If all children are in scope, return this.
  if(findstart==tree.branch_addresses.begin() &&
     findlim==tree.branch_addresses.end())
    return this_block;

  // Find the child code_blockt where the queried range begins:
  auto child_iter = this_block.statements().begin();
  // Skip any top-of-block declarations;
  // all other children are labelled subblocks.
  while(child_iter != this_block.statements().end() &&
        child_iter->get_statement() == ID_decl)
    ++child_iter;
  assert(child_iter != this_block.statements().end());
  std::advance(child_iter, child_offset);
  assert(child_iter != this_block.statements().end());
  auto &child_label=to_code_label(*child_iter);
  auto &child_block=to_code_block(child_label.code());

  bool single_child(afterstart==findlim);
  if(single_child)
  {
    // Range wholly contained within a child block
    return get_or_create_block_for_pcrange(
      tree.branch[child_offset],
      child_block,
      address_start,
      address_limit,
      findlim_block_start_address,
      amap,
      allow_merge);
  }

  // Otherwise we're being asked for a range of subblocks, but not all of them.
  // If it's legal to draw a new lexical scope around the requested subset,
  // do so; otherwise just return this block.

  // This can be a new lexical scope if all incoming edges target the
  // new block header, or come from within the suggested new block.

  // If modifying the block tree is forbidden, give up and return this:
  if(!allow_merge)
    return this_block;

  // Check for incoming control-flow edges targeting non-header
  // blocks of the new proposed block range:
  auto checkit=amap.find(*findstart);
  assert(checkit!=amap.end());
  ++checkit; // Skip the header, which can have incoming edges from outside.
  for(;
      checkit!=amap.end() && (checkit->first)<(findlim_block_start_address);
      ++checkit)
  {
    for(auto p : checkit->second.predecessors)
    {
      if(p<(*findstart) || p>=findlim_block_start_address)
      {
        log.debug() << "Generating codet:  "
                    << "warning: refusing to create lexical block spanning "
                    << (*findstart) << "-" << findlim_block_start_address
                    << " due to incoming edge " << p << " -> " << checkit->first
                    << messaget::eom;
        return this_block;
      }
    }
  }

  // All incoming edges are acceptable! Create a new block wrapping
  // the relevant children. Borrow the header block's label, and redirect
  // any block-internal edges to target the inner header block.

  const irep_idt child_label_name=child_label.get_label();
  std::string new_label_str = id2string(child_label_name);
  new_label_str+='$';
  irep_idt new_label_irep(new_label_str);

  code_labelt newlabel(child_label_name, code_blockt());
  code_blockt &newblock=to_code_block(newlabel.code());
  auto nblocks=std::distance(findstart, findlim);
  assert(nblocks>=2);
  log.debug() << "Generating codet:  combining "
              << std::distance(findstart, findlim) << " blocks for addresses "
              << (*findstart) << "-" << findlim_block_start_address
              << messaget::eom;

  // Make a new block containing every child of interest:
  auto &this_block_children = this_block.statements();
  assert(tree.branch.size()==this_block_children.size());
  for(auto blockidx=child_offset, blocklim=child_offset+nblocks;
      blockidx!=blocklim;
      ++blockidx)
    newblock.add(this_block_children[blockidx]);

  // Relabel the inner header:
  to_code_label(newblock.statements()[0]).set_label(new_label_irep);
  // Relabel internal gotos:
  replace_goto_target(newblock, child_label_name, new_label_irep);

  // Remove the now-empty sibling blocks:
  auto delfirst=this_block_children.begin();
  std::advance(delfirst, child_offset+1);
  auto dellim=delfirst;
  std::advance(dellim, nblocks-1);
  this_block_children.erase(delfirst, dellim);
  this_block_children[child_offset].swap(newlabel);

  // Perform the same transformation on the index tree:
  block_tree_nodet newnode;
  auto branchstart=tree.branch.begin();
  std::advance(branchstart, child_offset);
  auto branchlim=branchstart;
  std::advance(branchlim, nblocks);
  for(auto branchiter=branchstart; branchiter!=branchlim; ++branchiter)
    newnode.branch.push_back(std::move(*branchiter));
  ++branchstart;
  tree.branch.erase(branchstart, branchlim);

  assert(tree.branch.size()==this_block_children.size());

  auto branchaddriter=tree.branch_addresses.begin();
  std::advance(branchaddriter, child_offset);
  auto branchaddrlim=branchaddriter;
  std::advance(branchaddrlim, nblocks);
  newnode.branch_addresses.insert(
    newnode.branch_addresses.begin(),
    branchaddriter,
    branchaddrlim);

  ++branchaddriter;
  tree.branch_addresses.erase(branchaddriter, branchaddrlim);

  tree.branch[child_offset]=std::move(newnode);

  assert(tree.branch.size()==tree.branch_addresses.size());

  return
    to_code_block(
      to_code_label(
        this_block_children[child_offset]).code());
}

static void gather_symbol_live_ranges(
  java_bytecode_convert_methodt::method_offsett pc,
  const exprt &e,
  std::map<irep_idt, java_bytecode_convert_methodt::variablet> &result)
{
  if(e.id()==ID_symbol)
  {
    const auto &symexpr=to_symbol_expr(e);
    auto findit = result.emplace(
      std::piecewise_construct,
      std::forward_as_tuple(symexpr.get_identifier()),
      std::forward_as_tuple(symexpr, pc, 1));
    if(!findit.second)
    {
      auto &var = findit.first->second;

      if(pc<var.start_pc)
      {
        var.length+=(var.start_pc-pc);
        var.start_pc=pc;
      }
      else
      {
        var.length=std::max(var.length, (pc-var.start_pc)+1);
      }
    }
  }
  else
  {
    forall_operands(it, e)
      gather_symbol_live_ranges(pc, *it, result);
  }
}

/// Each static access to classname should be prefixed with a check for
/// necessary static init; this returns a call implementing that check.
/// \param classname: Class name
/// \return Returns a function call to the given class' static initializer
///   wrapper if one is needed, or a skip instruction otherwise.
codet java_bytecode_convert_methodt::get_clinit_call(
  const irep_idt &classname)
{
  auto findit = symbol_table.symbols.find(clinit_wrapper_name(classname));
  if(findit == symbol_table.symbols.end())
    return code_skipt();
  else
  {
    const code_function_callt ret(findit->second.symbol_expr());
    if(needed_lazy_methods)
      needed_lazy_methods->add_needed_method(findit->second.name);
    return ret;
  }
}

static std::size_t get_bytecode_type_width(const typet &ty)
{
  if(ty.id()==ID_pointer)
    return 32;
  return to_bitvector_type(ty).get_width();
}

code_blockt java_bytecode_convert_methodt::convert_parameter_annotations(
  const methodt &method,
  const java_method_typet &method_type)
{
  code_blockt code;

  // Consider parameter annotations
  const java_method_typet::parameterst &parameters(method_type.parameters());
  std::size_t param_index = method_type.has_this() ? 1 : 0;
  DATA_INVARIANT(
    parameters.size() >= method.parameter_annotations.size() + param_index,
    "parameters and parameter annotations mismatch");
  for(const auto &param_annotations : method.parameter_annotations)
  {
    // NotNull annotations are not standardized. We support these:
    if(
      java_bytecode_parse_treet::find_annotation(
        param_annotations, "java::javax.validation.constraints.NotNull") ||
      java_bytecode_parse_treet::find_annotation(
        param_annotations, "java::org.jetbrains.annotations.NotNull") ||
      java_bytecode_parse_treet::find_annotation(
        param_annotations, "org.eclipse.jdt.annotation.NonNull") ||
      java_bytecode_parse_treet::find_annotation(
        param_annotations, "java::edu.umd.cs.findbugs.annotations.NonNull"))
    {
      const irep_idt &param_identifier =
        parameters[param_index].get_identifier();
      const symbolt &param_symbol = symbol_table.lookup_ref(param_identifier);
      const auto param_type =
        type_try_dynamic_cast<pointer_typet>(param_symbol.type);
      if(param_type)
      {
        code_assertt code_assert(notequal_exprt(
          param_symbol.symbol_expr(), null_pointer_exprt(*param_type)));
        source_locationt check_loc = method.source_location;
        check_loc.set_comment("Not null annotation check");
        check_loc.set_property_class("not-null-annotation-check");
        code_assert.add_source_location() = check_loc;

        code.add(std::move(code_assert));
      }
    }
    ++param_index;
  }

  return code;
}

code_blockt
java_bytecode_convert_methodt::convert_instructions(const methodt &method)
{
  const instructionst &instructions=method.instructions;

  // Run a worklist algorithm, assuming that the bytecode has not
  // been tampered with. See "Leroy, X. (2003). Java bytecode
  // verification: algorithms and formalizations. Journal of Automated
  // Reasoning, 30(3-4), 235-269." for a more complete treatment.

  // first pass: get targets and map addresses to instructions

  address_mapt address_map;
  std::set<method_offsett> targets;

  std::vector<method_offsett> jsr_ret_targets;
  std::vector<instructionst::const_iterator> ret_instructions;

  for(auto i_it = instructions.begin(); i_it != instructions.end(); i_it++)
  {
    converted_instructiont ins=converted_instructiont(i_it, code_skipt());
    std::pair<address_mapt::iterator, bool> a_entry=
      address_map.insert(std::make_pair(i_it->address, ins));
    assert(a_entry.second);
    // addresses are strictly increasing, hence we must have inserted
    // a new maximal key
    assert(a_entry.first==--address_map.end());

    const auto bytecode = i_it->bytecode;
    const std::string statement = bytecode_info[i_it->bytecode].mnemonic;

    // clang-format off
    if(bytecode != BC_goto &&
       bytecode != BC_return &&
       bytecode != patternt("?return") &&
       bytecode != BC_athrow &&
       bytecode != BC_jsr &&
       bytecode != BC_jsr_w &&
       bytecode != BC_ret)
    {
      // clang-format on
      instructionst::const_iterator next=i_it;
      if(++next!=instructions.end())
        a_entry.first->second.successors.push_back(next->address);
    }

    // clang-format off
    if(bytecode == BC_athrow ||
       bytecode == BC_putfield ||
       bytecode == BC_getfield ||
       bytecode == BC_checkcast ||
       bytecode == BC_newarray ||
       bytecode == BC_anewarray ||
       bytecode == BC_idiv ||
       bytecode == BC_ldiv ||
       bytecode == BC_irem ||
       bytecode == BC_lrem ||
       bytecode == patternt("?astore") ||
       bytecode == patternt("?aload") ||
       bytecode == BC_invokestatic ||
       bytecode == BC_invokevirtual ||
       bytecode == BC_invokespecial ||
       bytecode == BC_invokeinterface ||
       (threading_support &&
        (bytecode == BC_monitorenter || bytecode == BC_monitorexit)))
    {
      // clang-format on
      const std::vector<method_offsett> handler =
        try_catch_handler(i_it->address, method.exception_table);
      std::list<method_offsett> &successors = a_entry.first->second.successors;
      successors.insert(successors.end(), handler.begin(), handler.end());
      targets.insert(handler.begin(), handler.end());
    }

    // clang-format off
    if(bytecode == BC_goto ||
       bytecode == patternt("if_?cmp??") ||
       bytecode == patternt("if??") ||
       bytecode == BC_ifnonnull ||
       bytecode == BC_ifnull ||
       bytecode == BC_jsr ||
       bytecode == BC_jsr_w)
    {
      // clang-format on
      PRECONDITION(!i_it->args.empty());

      auto target = numeric_cast_v<unsigned>(to_constant_expr(i_it->args[0]));
      targets.insert(target);

      a_entry.first->second.successors.push_back(target);

      if(bytecode == BC_jsr || bytecode == BC_jsr_w)
      {
        auto next = std::next(i_it);
        DATA_INVARIANT(
          next != instructions.end(), "jsr should have valid return address");
        targets.insert(next->address);
        jsr_ret_targets.push_back(next->address);
      }
    }
    else if(bytecode == BC_tableswitch || bytecode == BC_lookupswitch)
    {
      bool is_label=true;
      for(const auto &arg : i_it->args)
      {
        if(is_label)
        {
          auto target = numeric_cast_v<unsigned>(to_constant_expr(arg));
          targets.insert(target);
          a_entry.first->second.successors.push_back(target);
        }
        is_label=!is_label;
      }
    }
    else if(bytecode == BC_ret)
    {
      // Finish these later, once we've seen all jsr instructions.
      ret_instructions.push_back(i_it);
    }
  }
  draw_edges_from_ret_to_jsr(address_map, jsr_ret_targets, ret_instructions);

  for(const auto &address : address_map)
  {
    for(auto s : address.second.successors)
    {
      const auto a_it = address_map.find(s);
      CHECK_RETURN(a_it != address_map.end());
      a_it->second.predecessors.insert(address.first);
    }
  }

  // Clean the list of temporary variables created by a call to `tmp_variable`.
  // These are local variables in the goto function used to represent temporary
  // values of the JVM operand stack, newly allocated objects before the
  // constructor is called, ...
  tmp_vars.clear();

  // Now that the control flow graph is built, set up our local variables
  // (these require the graph to determine live ranges)
  setup_local_variables(method, address_map);

  std::set<method_offsett> working_set;

  if(!instructions.empty())
    working_set.insert(instructions.front().address);

  while(!working_set.empty())
  {
    auto cur = working_set.begin();
    auto address_it = address_map.find(*cur);
    CHECK_RETURN(address_it != address_map.end());
    auto &instruction = address_it->second;
    const method_offsett cur_pc = *cur;
    working_set.erase(cur);

    if(instruction.done)
      continue;
    working_set.insert(
      instruction.successors.begin(), instruction.successors.end());

    instructionst::const_iterator i_it = instruction.source;
    stack.swap(instruction.stack);
    instruction.stack.clear();
    codet &c = instruction.code;

    assert(
      stack.empty() || instruction.predecessors.size() <= 1 ||
      has_prefix(stack.front().get_string(ID_C_base_name), "$stack"));

    exprt arg0=i_it->args.size()>=1?i_it->args[0]:nil_exprt();
    exprt arg1=i_it->args.size()>=2?i_it->args[1]:nil_exprt();

    const auto bytecode = i_it->bytecode;
    const bytecode_infot &stmt_bytecode_info = bytecode_info[i_it->bytecode];
    const std::string statement = stmt_bytecode_info.mnemonic;

    // deal with _idx suffixes
    if(statement.size()>=2 &&
       statement[statement.size()-2]=='_' &&
       isdigit(statement[statement.size()-1]))
    {
      arg0=
        from_integer(
          string2integer(
            std::string(id2string(statement), statement.size()-1, 1)),
          java_int_type());
    }

    typet catch_type;

    // Find catch blocks that begin here. For now we assume if more than
    // one catch targets the same bytecode then we must be indifferent to
    // its type and just call it a Throwable.
    auto it=method.exception_table.begin();
    for(; it!=method.exception_table.end(); ++it)
    {
      if(cur_pc==it->handler_pc)
      {
        if(
          catch_type != typet() ||
          it->catch_type == struct_tag_typet(irep_idt()))
        {
          catch_type = struct_tag_typet("java::java.lang.Throwable");
          break;
        }
        else
          catch_type=it->catch_type;
      }
    }

    optionalt<codet> catch_instruction;

    if(catch_type!=typet())
    {
      // at the beginning of a handler, clear the stack and
      // push the corresponding exceptional return variable
      // We also create a catch exception instruction that
      // precedes the catch block, and which remove_exceptionst
      // will transform into something like:
      // catch_var = GLOBAL_THROWN_EXCEPTION;
      // GLOBAL_THROWN_EXCEPTION = null;
      stack.clear();
      symbol_exprt catch_var=
        tmp_variable(
          "caught_exception",
          java_reference_type(catch_type));
      stack.push_back(catch_var);
      catch_instruction = code_landingpadt(catch_var);
    }

    exprt::operandst op = pop(stmt_bytecode_info.pop);
    exprt::operandst results;
    results.resize(stmt_bytecode_info.push, nil_exprt());

    if(bytecode == BC_aconst_null)
    {
      assert(results.size()==1);
      results[0] = null_pointer_exprt(java_reference_type(java_void_type()));
    }
    else if(bytecode == BC_athrow)
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);
      convert_athrow(i_it->source_location, op, c, results);
    }
    else if(bytecode == BC_checkcast)
    {
      // checkcast throws an exception in case a cast of object
      // on stack to given type fails.
      // The stack isn't modified.
      PRECONDITION(op.size() == 1 && results.size() == 1);
      convert_checkcast(arg0, op, c, results);
    }
    else if(bytecode == BC_invokedynamic)
    {
      if(
        const auto res =
          convert_invoke_dynamic(i_it->source_location, i_it->address, arg0, c))
      {
        results.resize(1);
        results[0] = *res;
      }
    }
    else if(
      bytecode == BC_invokestatic && id2string(arg0.get(ID_identifier)) ==
                                       "java::org.cprover.CProver.assume:(Z)V")
    {
      const java_method_typet &method_type = to_java_method_type(arg0.type());
      INVARIANT(
        method_type.parameters().size() == 1,
        "function expected to have exactly one parameter");
      c = replace_call_to_cprover_assume(i_it->source_location, c);
    }
    // replace calls to CProver.atomicBegin
    else if(
      bytecode == BC_invokestatic &&
      arg0.get(ID_identifier) == "java::org.cprover.CProver.atomicBegin:()V")
    {
      c = codet(ID_atomic_begin);
    }
    // replace calls to CProver.atomicEnd
    else if(
      bytecode == BC_invokestatic &&
      arg0.get(ID_identifier) == "java::org.cprover.CProver.atomicEnd:()V")
    {
      c = codet(ID_atomic_end);
    }
    else if(
      bytecode == BC_invokeinterface || bytecode == BC_invokespecial ||
      bytecode == BC_invokevirtual || bytecode == BC_invokestatic)
    {
      class_method_descriptor_exprt *class_method_descriptor =
        expr_try_dynamic_cast<class_method_descriptor_exprt>(arg0);

      INVARIANT(
        class_method_descriptor,
        "invokeinterface, invokespecial, invokevirtual and invokestatic should "
        "be called with a class method descriptor expression as arg0");

      convert_invoke(
        i_it->source_location, statement, *class_method_descriptor, c, results);
    }
    else if(bytecode == BC_return)
    {
      PRECONDITION(op.empty() && results.empty());
      c = code_frontend_returnt();
    }
    else if(bytecode == patternt("?return"))
    {
      // Return types are promoted in java, so this might need
      // conversion.
      PRECONDITION(op.size() == 1 && results.empty());
      const exprt r =
        typecast_exprt::conditional_cast(op[0], method_return_type);
      c = code_frontend_returnt(r);
    }
    else if(bytecode == patternt("?astore"))
    {
      PRECONDITION(results.empty());
      c = convert_astore(statement, op, i_it->source_location);
    }
    else if(bytecode == patternt("?store") || bytecode == patternt("?store_?"))
    {
      // store value into some local variable
      PRECONDITION(op.size() == 1 && results.empty());
      c = convert_store(
        statement, arg0, op, i_it->address, i_it->source_location);
    }
    else if(bytecode == patternt("?aload"))
    {
      PRECONDITION(results.size() == 1);
      results[0] = convert_aload(statement, op);
    }
    else if(bytecode == patternt("?load") || bytecode == patternt("?load_?"))
    {
      // load a value from a local variable
      results[0] = convert_load(arg0, statement[0], i_it->address);
    }
    else if(bytecode == BC_ldc || bytecode == BC_ldc_w || bytecode == BC_ldc2_w)
    {
      PRECONDITION(op.empty() && results.size() == 1);

      INVARIANT(
        !can_cast_expr<java_string_literal_exprt>(arg0) && arg0.id() != ID_type,
        "String and Class literals should have been lowered in "
        "generate_constant_global_variables");

      results[0] = arg0;
    }
    else if(bytecode == BC_goto || bytecode == BC_goto_w)
    {
      PRECONDITION(op.empty() && results.empty());
      const mp_integer number =
        numeric_cast_v<mp_integer>(to_constant_expr(arg0));
      code_gotot code_goto(label(integer2string(number)));
      c=code_goto;
    }
    else if(bytecode == BC_jsr || bytecode == BC_jsr_w)
    {
      // As 'goto', except we must also push the subroutine return address:
      PRECONDITION(op.empty() && results.size() == 1);
      const mp_integer number =
        numeric_cast_v<mp_integer>(to_constant_expr(arg0));
      code_gotot code_goto(label(integer2string(number)));
      c=code_goto;
      results[0]=
        from_integer(
          std::next(i_it)->address,
          unsignedbv_typet(64));
      results[0].type() = pointer_type(java_void_type());
    }
    else if(bytecode == BC_ret)
    {
      // Since we have a bounded target set, make life easier on our analyses
      // and write something like:
      // if(retaddr==5) goto 5; else if(retaddr==10) goto 10; ...
      PRECONDITION(op.empty() && results.empty());
      assert(!jsr_ret_targets.empty());
      c = convert_ret(
        jsr_ret_targets, arg0, i_it->source_location, i_it->address);
    }
    else if(bytecode == BC_iconst_m1)
    {
      assert(results.size()==1);
      results[0]=from_integer(-1, java_int_type());
    }
    else if(bytecode == patternt("?const_?"))
    {
      assert(results.size()==1);
      results = convert_const(statement, to_constant_expr(arg0), results);
    }
    else if(bytecode == patternt("?ipush"))
    {
      PRECONDITION(results.size()==1);
      DATA_INVARIANT(
        arg0.id()==ID_constant,
        "ipush argument expected to be constant");
      results[0] = typecast_exprt::conditional_cast(arg0, java_int_type());
    }
    else if(bytecode == patternt("if_?cmp??"))
    {
      PRECONDITION(op.size() == 2 && results.empty());
      const mp_integer number =
        numeric_cast_v<mp_integer>(to_constant_expr(arg0));
      c = convert_if_cmp(
        address_map, bytecode, op, number, i_it->source_location);
    }
    else if(bytecode == patternt("if??"))
    {
      // clang-format off
      const irep_idt id=
        bytecode == BC_ifeq ? ID_equal :
        bytecode == BC_ifne ? ID_notequal :
        bytecode == BC_iflt ? ID_lt :
        bytecode == BC_ifge ? ID_ge :
        bytecode == BC_ifgt ? ID_gt :
        bytecode == BC_ifle ? ID_le :
        irep_idt();
      // clang-format on

      INVARIANT(!id.empty(), "unexpected bytecode-if");
      PRECONDITION(op.size() == 1 && results.empty());
      const mp_integer number =
        numeric_cast_v<mp_integer>(to_constant_expr(arg0));
      c = convert_if(address_map, op, id, number, i_it->source_location);
    }
    else if(bytecode == patternt("ifnonnull"))
    {
      PRECONDITION(op.size() == 1 && results.empty());
      const mp_integer number =
        numeric_cast_v<mp_integer>(to_constant_expr(arg0));
      c = convert_ifnonull(address_map, op, number, i_it->source_location);
    }
    else if(bytecode == patternt("ifnull"))
    {
      PRECONDITION(op.size() == 1 && results.empty());
      const mp_integer number =
        numeric_cast_v<mp_integer>(to_constant_expr(arg0));
      c = convert_ifnull(address_map, op, number, i_it->source_location);
    }
    else if(bytecode == BC_iinc)
    {
      c = convert_iinc(arg0, arg1, i_it->source_location, i_it->address);
    }
    else if(bytecode == patternt("?xor"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=bitxor_exprt(op[0], op[1]);
    }
    else if(bytecode == patternt("?or"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=bitor_exprt(op[0], op[1]);
    }
    else if(bytecode == patternt("?and"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=bitand_exprt(op[0], op[1]);
    }
    else if(bytecode == patternt("?shl"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results = convert_shl(statement, op, results);
    }
    else if(bytecode == patternt("?shr"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=ashr_exprt(op[0], op[1]);
    }
    else if(bytecode == patternt("?ushr"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results = convert_ushr(statement, op, results);
    }
    else if(bytecode == patternt("?add"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=plus_exprt(op[0], op[1]);
    }
    else if(bytecode == patternt("?sub"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=minus_exprt(op[0], op[1]);
    }
    else if(bytecode == patternt("?div"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=div_exprt(op[0], op[1]);
    }
    else if(bytecode == patternt("?mul"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=mult_exprt(op[0], op[1]);
    }
    else if(bytecode == patternt("?neg"))
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);
      results[0]=unary_minus_exprt(op[0], op[0].type());
    }
    else if(bytecode == patternt("?rem"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      // This is _not_ the remainder operation defined by IEEE 754,
      // but similar to the fmod C library function.
      if(bytecode == BC_frem || bytecode == BC_drem)
        results[0] = binary_exprt(op[0], ID_floatbv_mod, op[1]);
      else
        results[0]=mod_exprt(op[0], op[1]);
    }
    else if(bytecode == patternt("?cmp"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results = convert_cmp(op, results);
    }
    else if(bytecode == patternt("?cmp?"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results = convert_cmp2(statement, op, results);
    }
    else if(bytecode == patternt("?cmpl"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=binary_relation_exprt(op[0], ID_lt, op[1]);
    }
    else if(bytecode == BC_dup)
    {
      PRECONDITION(op.size() == 1 && results.size() == 2);
      results[0]=results[1]=op[0];
    }
    else if(bytecode == BC_dup_x1)
    {
      PRECONDITION(op.size() == 2 && results.size() == 3);
      results[0]=op[1];
      results[1]=op[0];
      results[2]=op[1];
    }
    else if(bytecode == BC_dup_x2)
    {
      PRECONDITION(op.size() == 3 && results.size() == 4);
      results[0]=op[2];
      results[1]=op[0];
      results[2]=op[1];
      results[3]=op[2];
    }
    // dup2* behaviour depends on the size of the operands on the
    // stack
    else if(bytecode == BC_dup2)
    {
      PRECONDITION(!stack.empty() && results.empty());
      convert_dup2(op, results);
    }
    else if(bytecode == BC_dup2_x1)
    {
      PRECONDITION(!stack.empty() && results.empty());
      convert_dup2_x1(op, results);
    }
    else if(bytecode == BC_dup2_x2)
    {
      PRECONDITION(!stack.empty() && results.empty());
      convert_dup2_x2(op, results);
    }
    else if(bytecode == BC_getfield)
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);
      results[0] = java_bytecode_promotion(
        to_member(op[0], expr_dynamic_cast<fieldref_exprt>(arg0), ns));
    }
    else if(bytecode == BC_getstatic)
    {
      PRECONDITION(op.empty() && results.size() == 1);
      const auto &field_name=arg0.get_string(ID_component_name);
      const bool is_assertions_disabled_field=
        field_name.find("$assertionsDisabled")!=std::string::npos;

      const irep_idt field_id(
        get_static_field(arg0.get_string(ID_class), field_name));

      // Symbol should have been populated by java_bytecode_convert_class:
      const symbol_exprt symbol_expr(
        symbol_table.lookup_ref(field_id).symbol_expr());

      convert_getstatic(
        i_it->source_location,
        arg0,
        symbol_expr,
        is_assertions_disabled_field,
        c,
        results);
    }
    else if(bytecode == BC_putfield)
    {
      PRECONDITION(op.size() == 2 && results.empty());
      c = convert_putfield(expr_dynamic_cast<fieldref_exprt>(arg0), op);
    }
    else if(bytecode == BC_putstatic)
    {
      PRECONDITION(op.size() == 1 && results.empty());
      const auto &field_name=arg0.get_string(ID_component_name);

      const irep_idt field_id(
        get_static_field(arg0.get_string(ID_class), field_name));

      // Symbol should have been populated by java_bytecode_convert_class:
      const symbol_exprt symbol_expr(
        symbol_table.lookup_ref(field_id).symbol_expr());

      c = convert_putstatic(i_it->source_location, arg0, op, symbol_expr);
    }
    else if(
      bytecode == BC_f2i || bytecode == BC_f2l || bytecode == BC_d2i ||
      bytecode == BC_d2l)
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);
      typet src_type = java_type_from_char(statement[0]);
      typet dest_type = java_type_from_char(statement[2]);

      // See JLS 5.1.3. Narrowing Primitive Conversion
      // +-NaN is converted to 0
      // +-Inf resp. values beyond the int/long range
      //   are mapped to max/min of int/long.
      // Other values are rounded towards zero

      // for int: 2147483647, for long: 9223372036854775807L
      exprt largest_as_dest =
        to_integer_bitvector_type(dest_type).largest_expr();

      // 2147483647 is not exactly representable in float;
      // it will be rounded up to 2147483648, which is fine.
      // 9223372036854775807L is not exactly representable
      // neither in float nor in double; it is rounded up to
      // 9223372036854775808.0, which is fine.
      exprt largest_as_src =
        from_integer(to_integer_bitvector_type(dest_type).largest(), src_type);

      // for int: -2147483648, for long: -9223372036854775808L
      exprt smallest_as_dest =
        to_integer_bitvector_type(dest_type).smallest_expr();

      // -2147483648 and -9223372036854775808L are exactly
      // representable in float and double.
      exprt smallest_as_src =
        from_integer(to_integer_bitvector_type(dest_type).smallest(), src_type);

      results[0] = if_exprt(
        binary_relation_exprt(op[0], ID_le, smallest_as_src),
        smallest_as_dest,
        if_exprt(
          binary_relation_exprt(op[0], ID_ge, largest_as_src),
          largest_as_dest,
          typecast_exprt::conditional_cast(op[0], dest_type)));
    }
    else if(bytecode == patternt("?2?")) // i2c etc.
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);
      typet type=java_type_from_char(statement[2]);
      results[0] = typecast_exprt::conditional_cast(op[0], type);

      // These types get converted/truncated then immediately turned back into
      // ints again, so we just double-cast here.
      if(
        type == java_char_type() || type == java_byte_type() ||
        type == java_short_type())
      {
        results[0] = typecast_exprt(results[0], java_int_type());
      }
    }
    else if(bytecode == BC_new)
    {
      // use temporary since the stack symbol might get duplicated
      PRECONDITION(op.empty() && results.size() == 1);
      convert_new(i_it->source_location, arg0, c, results);
    }
    else if(bytecode == BC_newarray || bytecode == BC_anewarray)
    {
      // the op is the array size
      PRECONDITION(op.size() == 1 && results.size() == 1);
      c = convert_newarray(i_it->source_location, statement, arg0, op, results);
    }
    else if(bytecode == BC_multianewarray)
    {
      // The first argument is the type, the second argument is the number of
      // dimensions.  The size of each dimension is on the stack.
      const std::size_t dimension =
        numeric_cast_v<std::size_t>(to_constant_expr(arg1));

      op=pop(dimension);
      assert(results.size()==1);
      c = convert_multianewarray(i_it->source_location, arg0, op, results);
    }
    else if(bytecode == BC_arraylength)
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);

      // any array type is fine here, so we go for a reference array
      dereference_exprt array{typecast_exprt{op[0], java_array_type('a')}};
      PRECONDITION(array.type().id() == ID_struct_tag);
      array.set(ID_java_member_access, true);

      results[0] = member_exprt{std::move(array), "length", java_int_type()};
    }
    else if(bytecode == BC_tableswitch || bytecode == BC_lookupswitch)
    {
      PRECONDITION(op.size() == 1 && results.empty());
      c = convert_switch(op, i_it->args, i_it->source_location);
    }
    else if(bytecode == BC_pop || bytecode == BC_pop2)
    {
      c = convert_pop(statement, op);
    }
    else if(bytecode == BC_instanceof)
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);

      results[0] =
        java_instanceof_exprt(op[0], to_struct_tag_type(arg0.type()));
    }
    else if(bytecode == BC_monitorenter || bytecode == BC_monitorexit)
    {
      c = convert_monitorenterexit(statement, op, i_it->source_location);
    }
    else if(bytecode == BC_swap)
    {
      PRECONDITION(op.size() == 2 && results.size() == 2);
      results[1]=op[0];
      results[0]=op[1];
    }
    else if(bytecode == BC_nop)
    {
      c=code_skipt();
    }
    else
    {
      c=codet(statement);
      c.operands()=op;
    }

    c = do_exception_handling(method, working_set, cur_pc, c);

    // Finally if this is the beginning of a catch block (already determined
    // before the big bytecode switch), insert the exception 'landing pad'
    // instruction before the actual instruction:
    if(catch_instruction.has_value())
    {
      if(c.get_statement() != ID_block)
        c = code_blockt{{c}};
      c.operands().insert(c.operands().begin(), *catch_instruction);
    }

    if(!i_it->source_location.get_line().empty())
      merge_source_location_rec(c, i_it->source_location);

    push(results);

    instruction.done = true;
    for(const auto address : instruction.successors)
    {
      address_mapt::iterator a_it2=address_map.find(address);
      CHECK_RETURN(a_it2 != address_map.end());

      // clear the stack if this is an exception handler
      for(const auto &exception_row : method.exception_table)
      {
        if(address==exception_row.handler_pc)
        {
          stack.clear();
          break;
        }
      }

      if(!stack.empty() && a_it2->second.predecessors.size()>1)
      {
        // copy into temporaries
        code_blockt more_code;

        // introduce temporaries when successor is seen for the first
        // time
        if(a_it2->second.stack.empty())
        {
          for(stackt::iterator s_it=stack.begin();
              s_it!=stack.end();
              ++s_it)
          {
            symbol_exprt lhs=tmp_variable("$stack", s_it->type());
            code_assignt a(lhs, *s_it);
            more_code.add(a);

            s_it->swap(lhs);
          }
        }
        else
        {
          INVARIANT(
            a_it2->second.stack.size() == stack.size(),
            "Stack sizes should be the same.");
          stackt::const_iterator os_it=a_it2->second.stack.begin();
          for(auto &expr : stack)
          {
            assert(has_prefix(os_it->get_string(ID_C_base_name), "$stack"));
            symbol_exprt lhs=to_symbol_expr(*os_it);
            code_assignt a(lhs, expr);
            more_code.add(a);

            expr.swap(lhs);
            ++os_it;
          }
        }

        if(results.empty())
        {
          more_code.add(c);
          c.swap(more_code);
        }
        else
        {
          if(c.get_statement() != ID_block)
            c = code_blockt{{c}};

          auto &last_statement=to_code_block(c).find_last_statement();
          if(last_statement.get_statement()==ID_goto)
          {
            // Insert stack twiddling before branch:
            if(last_statement.get_statement() != ID_block)
              last_statement = code_blockt{{last_statement}};

            last_statement.operands().insert(
              last_statement.operands().begin(),
              more_code.statements().begin(),
              more_code.statements().end());
          }
          else
            to_code_block(c).append(more_code);
        }
      }
      a_it2->second.stack=stack;
    }
  }

  code_blockt code;

  // Add anonymous locals to the symtab:
  for(const auto &var : used_local_names)
  {
    symbolt new_symbol;
    new_symbol.name=var.get_identifier();
    new_symbol.type=var.type();
    new_symbol.base_name=var.get(ID_C_base_name);
    new_symbol.pretty_name=strip_java_namespace_prefix(var.get_identifier());
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;
    new_symbol.is_file_local=true;
    new_symbol.is_thread_local=true;
    new_symbol.is_lvalue=true;
    symbol_table.add(new_symbol);
  }

  // Try to recover block structure as indicated in the local variable table:

  // The block tree node mirrors the block structure of root_block,
  // indexing the Java PCs where each subblock starts and ends.
  block_tree_nodet root;
  code_blockt root_block;

  // First create a simple flat list of basic blocks. We'll add lexical nesting
  // constructs as variable live-ranges require next.
  bool start_new_block=true;
  bool has_seen_previous_address=false;
  method_offsett previous_address = 0;
  for(const auto &address_pair : address_map)
  {
    const method_offsett address = address_pair.first;
    assert(address_pair.first==address_pair.second.source->address);
    const codet &c=address_pair.second.code;

    // Start a new lexical block if this is a branch target:
    if(!start_new_block)
      start_new_block=targets.find(address)!=targets.end();
    // Start a new lexical block if this is a control flow join
    // (e.g. due to exceptional control flow)
    if(!start_new_block)
      start_new_block=address_pair.second.predecessors.size()>1;
    // Start a new lexical block if we've just entered a block in which
    // exceptions are handled. This is usually the start of a try block, but a
    // single try can be represented as multiple non-contiguous blocks in the
    // exception table.
    if(!start_new_block && has_seen_previous_address)
    {
      for(const auto &exception_row : method.exception_table)
        if(exception_row.start_pc==previous_address)
        {
          start_new_block=true;
          break;
        }
    }

    if(start_new_block)
    {
      root_block.add(
        code_labelt{label(std::to_string(address)), code_blockt{}});
      root.branch.push_back(block_tree_nodet::get_leaf());
      assert((root.branch_addresses.empty() ||
              root.branch_addresses.back()<address) &&
             "Block addresses should be unique and increasing");
      root.branch_addresses.push_back(address);
    }

    if(c.get_statement()!=ID_skip)
    {
      auto &lastlabel = to_code_label(root_block.statements().back());
      auto &add_to_block=to_code_block(lastlabel.code());
      add_to_block.add(c);
    }
    start_new_block=address_pair.second.successors.size()>1;

    previous_address=address;
    has_seen_previous_address=true;
  }

  // Find out where temporaries are used:
  std::map<irep_idt, variablet> temporary_variable_live_ranges;
  for(const auto &aentry : address_map)
    gather_symbol_live_ranges(
      aentry.first,
      aentry.second.code,
      temporary_variable_live_ranges);

  std::vector<const variablet*> vars_to_process;
  for(const auto &vlist : variables)
    for(const auto &v : vlist)
      vars_to_process.push_back(&v);

  for(const auto &v : tmp_vars)
    vars_to_process.push_back(
      &temporary_variable_live_ranges.at(v.get_identifier()));

  for(const auto &v : used_local_names)
    vars_to_process.push_back(
      &temporary_variable_live_ranges.at(v.get_identifier()));

  for(const auto vp : vars_to_process)
  {
    const auto &v=*vp;
    if(v.is_parameter)
      continue;
    // Merge lexical scopes as far as possible to allow us to
    // declare these variable scopes faithfully.
    // Don't insert yet, as for the time being the blocks' only
    // operands must be other blocks.
    // The declarations will be inserted in the next pass instead.
    get_or_create_block_for_pcrange(
      root,
      root_block,
      v.start_pc,
      v.start_pc + v.length,
      std::numeric_limits<method_offsett>::max(),
      address_map);
  }
  for(const auto vp : vars_to_process)
  {
    const auto &v=*vp;
    if(v.is_parameter)
      continue;
    // Skip anonymous variables:
    if(v.symbol_expr.get_identifier().empty())
      continue;
    auto &block = get_block_for_pcrange(
      root,
      root_block,
      v.start_pc,
      v.start_pc + v.length,
      std::numeric_limits<method_offsett>::max());
    code_declt d(v.symbol_expr);
    block.statements().insert(block.statements().begin(), d);
  }

  for(auto &block : root_block.statements())
    code.add(block);

  return code;
}

codet java_bytecode_convert_methodt::convert_pop(
  const irep_idt &statement,
  const exprt::operandst &op)
{
  // these are skips
  codet c = code_skipt();

  // pop2 removes two single-word items from the stack (e.g. two
  // integers, or an integer and an object reference) or one
  // two-word item (i.e. a double or a long).
  // http://cs.au.dk/~mis/dOvs/jvmspec/ref-pop2.html
  if(statement == "pop2" && get_bytecode_type_width(op[0].type()) == 32)
    pop(1);
  return c;
}

code_switcht java_bytecode_convert_methodt::convert_switch(
  const exprt::operandst &op,
  const java_bytecode_parse_treet::instructiont::argst &args,
  const source_locationt &location)
{
  // we turn into switch-case
  code_blockt code_block;
  code_block.add_source_location() = location;

  bool is_label = true;
  for(auto a_it = args.begin(); a_it != args.end();
      a_it++, is_label = !is_label)
  {
    if(is_label)
    {
      const mp_integer number =
        numeric_cast_v<mp_integer>(to_constant_expr(*a_it));
      // The switch case does not contain any code, it just branches via a GOTO
      // to the jump target of the tableswitch/lookupswitch case at
      // hand. Therefore we consider this code to belong to the source bytecode
      // instruction and not the target instruction.
      const method_offsett label_number =
        numeric_cast_v<method_offsett>(number);
      code_gotot code(label(std::to_string(label_number)));
      code.add_source_location() = location;

      if(a_it == args.begin())
      {
        code_switch_caset code_case(nil_exprt(), std::move(code));
        code_case.set_default();

        code_block.add(std::move(code_case), location);
      }
      else
      {
        exprt case_op =
          typecast_exprt::conditional_cast(*std::prev(a_it), op[0].type());
        case_op.add_source_location() = location;

        code_switch_caset code_case(std::move(case_op), std::move(code));
        code_block.add(std::move(code_case), location);
      }
    }
  }

  code_switcht code_switch(op[0], std::move(code_block));
  code_switch.add_source_location() = location;
  return code_switch;
}

codet java_bytecode_convert_methodt::convert_monitorenterexit(
  const irep_idt &statement,
  const exprt::operandst &op,
  const source_locationt &source_location)
{
  const irep_idt descriptor = (statement == "monitorenter") ?
    "java::java.lang.Object.monitorenter:(Ljava/lang/Object;)V" :
    "java::java.lang.Object.monitorexit:(Ljava/lang/Object;)V";

  if(!threading_support || !symbol_table.has_symbol(descriptor))
    return code_skipt();

  // becomes a function call
  java_method_typet type(
    {java_method_typet::parametert(java_reference_type(java_void_type()))},
    java_void_type());
  code_function_callt call(symbol_exprt(descriptor, type), {op[0]});
  call.add_source_location() = source_location;
  if(needed_lazy_methods && symbol_table.has_symbol(descriptor))
    needed_lazy_methods->add_needed_method(descriptor);
  return std::move(call);
}

void java_bytecode_convert_methodt::convert_dup2(
  exprt::operandst &op,
  exprt::operandst &results)
{
  if(get_bytecode_type_width(stack.back().type()) == 32)
    op = pop(2);
  else
    op = pop(1);

  results.insert(results.end(), op.begin(), op.end());
  results.insert(results.end(), op.begin(), op.end());
}

void java_bytecode_convert_methodt::convert_dup2_x1(
  exprt::operandst &op,
  exprt::operandst &results)
{
  if(get_bytecode_type_width(stack.back().type()) == 32)
    op = pop(3);
  else
    op = pop(2);

  results.insert(results.end(), op.begin() + 1, op.end());
  results.insert(results.end(), op.begin(), op.end());
}

void java_bytecode_convert_methodt::convert_dup2_x2(
  exprt::operandst &op,
  exprt::operandst &results)
{
  if(get_bytecode_type_width(stack.back().type()) == 32)
    op = pop(2);
  else
    op = pop(1);

  exprt::operandst op2;

  if(get_bytecode_type_width(stack.back().type()) == 32)
    op2 = pop(2);
  else
    op2 = pop(1);

  results.insert(results.end(), op.begin(), op.end());
  results.insert(results.end(), op2.begin(), op2.end());
  results.insert(results.end(), op.begin(), op.end());
}

exprt::operandst &java_bytecode_convert_methodt::convert_const(
  const irep_idt &statement,
  const constant_exprt &arg0,
  exprt::operandst &results) const
{
  const char type_char = statement[0];
  const bool is_double('d' == type_char);
  const bool is_float('f' == type_char);

  if(is_double || is_float)
  {
    const ieee_float_spect spec(
      is_float ? ieee_float_spect::single_precision()
               : ieee_float_spect::double_precision());

    ieee_floatt value(spec);
    if(arg0.type().id() != ID_floatbv)
    {
      const mp_integer number = numeric_cast_v<mp_integer>(arg0);
      value.from_integer(number);
    }
    else
      value.from_expr(arg0);

    results[0] = value.to_expr();
  }
  else
  {
    const mp_integer value = numeric_cast_v<mp_integer>(arg0);
    const typet type = java_type_from_char(statement[0]);
    results[0] = from_integer(value, type);
  }
  return results;
}

static void adjust_invoke_argument_types(
  const java_method_typet::parameterst &parameters,
  code_function_callt::argumentst &arguments)
{
  // do some type adjustment for the arguments,
  // as Java promotes arguments
  // Also cast pointers since intermediate locals
  // can be void*.
  INVARIANT(
    parameters.size() == arguments.size(),
    "for each parameter there must be exactly one argument");
  for(std::size_t i = 0; i < parameters.size(); i++)
  {
    const typet &type = parameters[i].type();
    if(
      type == java_boolean_type() || type == java_char_type() ||
      type == java_byte_type() || type == java_short_type() ||
      type.id() == ID_pointer)
    {
      arguments[i] = typecast_exprt::conditional_cast(arguments[i], type);
    }
  }
}

void java_bytecode_convert_methodt::convert_invoke(
  source_locationt location,
  const irep_idt &statement,
  class_method_descriptor_exprt &class_method_descriptor,
  codet &c,
  exprt::operandst &results)
{
  const bool use_this(statement != "invokestatic");
  const bool is_virtual(
    statement == "invokevirtual" || statement == "invokeinterface");

  const irep_idt &invoked_method_id = class_method_descriptor.get_identifier();
  INVARIANT(
    !invoked_method_id.empty(),
    "invoke statement arg0 must have an identifier");

  auto method_symbol = symbol_table.symbols.find(invoked_method_id);

  // Use the most precise type available: the actual symbol has generic info,
  // whereas the type given by the invoke instruction doesn't and is therefore
  // less accurate.
  if(method_symbol != symbol_table.symbols.end())
  {
    // Note the number of parameters might change here due to constructors using
    // invokespecial will have zero arguments (the `this` is added below)
    // but the symbol for the <init> will have the this parameter.
    INVARIANT(
      to_java_method_type(class_method_descriptor.type()).return_type().id() ==
        to_code_type(method_symbol->second.type).return_type().id(),
      "Function return type must not change in kind");
    class_method_descriptor.type() = method_symbol->second.type;
  }

  // Note arg0 and arg0.type() are subject to many side-effects in this method,
  // then finally used to populate the call instruction.
  java_method_typet &method_type =
    to_java_method_type(class_method_descriptor.type());

  java_method_typet::parameterst &parameters(method_type.parameters());

  if(use_this)
  {
    const irep_idt class_id = class_method_descriptor.class_id();

    if(parameters.empty() || !parameters[0].get_this())
    {
      typet thistype = struct_tag_typet(class_id);
      reference_typet object_ref_type = java_reference_type(thistype);
      java_method_typet::parametert this_p(object_ref_type);
      this_p.set_this();
      this_p.set_base_name(ID_this);
      parameters.insert(parameters.begin(), this_p);
    }

    // Note invokespecial is used for super-method calls as well as
    // constructors.
    if(statement == "invokespecial")
    {
      if(is_constructor(invoked_method_id))
      {
        if(needed_lazy_methods)
          needed_lazy_methods->add_needed_class(class_id);
        method_type.set_is_constructor();
      }
      else
        method_type.set(ID_java_super_method_call, true);
    }
  }

  location.set_function(method_id);

  code_function_callt::argumentst arguments = pop(parameters.size());

  // double-check a bit
  INVARIANT(
    !use_this || arguments.front().type().id() == ID_pointer,
    "first argument must be a pointer");

  adjust_invoke_argument_types(parameters, arguments);

  // do some type adjustment for return values
  exprt lhs = nil_exprt();
  const typet &return_type = method_type.return_type();

  if(return_type.id() != ID_empty)
  {
    // return types are promoted in Java
    lhs = tmp_variable("return", return_type);
    exprt promoted = java_bytecode_promotion(lhs);
    results.resize(1);
    results[0] = promoted;
  }

  // If we don't have a definition for the called symbol, and we won't
  // inherit a definition from a super-class, we create a new symbol and
  // insert it in the symbol table. The name and type of the method are
  // derived from the information we have in the call.
  // We fix the access attribute to ID_private, because of the following
  // reasons:
  // - We don't know the original access attribute and since the .class file is
  //   unavailable, we have no way to know.
  // - The translated method could be an inherited protected method, hence
  //   accessible from the original caller, but not from the generated test.
  //   Therefore we must assume that the method is not accessible.
  // We set opaque methods as final to avoid assuming they can be overridden.
  if(
    method_symbol == symbol_table.symbols.end() &&
    !(is_virtual && is_method_inherited(
                      class_method_descriptor.class_id(),
                      class_method_descriptor.mangled_method_name())))
  {
    create_method_stub_symbol(
      invoked_method_id,
      class_method_descriptor.base_method_name(),
      id2string(class_method_descriptor.class_id()).substr(6) + "." +
        id2string(class_method_descriptor.base_method_name()) + "()",
      method_type,
      class_method_descriptor.class_id(),
      symbol_table,
      log.get_message_handler());
  }

  exprt function;
  if(is_virtual)
  {
    // dynamic binding
    PRECONDITION(use_this);
    PRECONDITION(!arguments.empty());
    function = class_method_descriptor;
    // Populate needed methods later,
    // once we know what object types can exist.
  }
  else
  {
    // static binding
    function = symbol_exprt(invoked_method_id, method_type);
    if(needed_lazy_methods)
    {
      needed_lazy_methods->add_needed_method(invoked_method_id);
      // Calling a static method causes static initialization:
      needed_lazy_methods->add_needed_class(class_method_descriptor.class_id());
    }
  }

  code_function_callt call(
    std::move(lhs), std::move(function), std::move(arguments));
  call.add_source_location() = location;
  call.function().add_source_location() = location;

  // Replacing call if it is a function of the Character library,
  // returning the same call otherwise
  c = string_preprocess.replace_character_call(call);

  if(!use_this)
  {
    codet clinit_call = get_clinit_call(class_method_descriptor.class_id());
    if(clinit_call.get_statement() != ID_skip)
      c = code_blockt({clinit_call, c});
  }
}

codet &java_bytecode_convert_methodt::replace_call_to_cprover_assume(
  source_locationt location,
  codet &c)
{
  exprt operand = pop(1)[0];

  // we may need to adjust the type of the argument
  operand = typecast_exprt::conditional_cast(operand, bool_typet());

  c = code_assumet(operand);
  location.set_function(method_id);
  c.add_source_location() = location;
  return c;
}

void java_bytecode_convert_methodt::convert_checkcast(
  const exprt &arg0,
  const exprt::operandst &op,
  codet &c,
  exprt::operandst &results) const
{
  java_instanceof_exprt check(op[0], to_struct_tag_type(arg0.type()));
  code_assertt assert_class(check);
  assert_class.add_source_location().set_comment("Dynamic cast check");
  assert_class.add_source_location().set_property_class("bad-dynamic-cast");
  // we add this assert such that we can recognise it
  // during the instrumentation phase
  c = std::move(assert_class);
  results[0] = op[0];
}

void java_bytecode_convert_methodt::convert_athrow(
  const source_locationt &location,
  const exprt::operandst &op,
  codet &c,
  exprt::operandst &results) const
{
  if(
    assert_no_exceptions_thrown ||
    ((uncaught_exceptions_domaint::get_exception_type(op[0].type()) ==
      "java::java.lang.AssertionError") &&
     !throw_assertion_error))
  {
    // we translate athrow into
    // ASSERT false;
    // ASSUME false:
    code_assertt assert_code(false_exprt{});
    source_locationt assert_location = location; // copy
    assert_location.set_comment("assertion at " + location.as_string());
    assert_location.set("user-provided", true);
    assert_location.set_property_class(ID_assertion);
    assert_code.add_source_location() = assert_location;

    code_assumet assume_code(false_exprt{});
    source_locationt assume_location = location; // copy
    assume_location.set("user-provided", true);
    assume_code.add_source_location() = assume_location;

    c = code_blockt({assert_code, assume_code});
  }
  else
  {
    side_effect_expr_throwt throw_expr(irept(), typet(), location);
    throw_expr.copy_to_operands(op[0]);
    c = code_expressiont(throw_expr);
  }
  results[0] = op[0];
}

codet &java_bytecode_convert_methodt::do_exception_handling(
  const java_bytecode_convert_methodt::methodt &method,
  const std::set<method_offsett> &working_set,
  method_offsett cur_pc,
  codet &code)
{
  // For each exception handler range that starts here add a CATCH-PUSH marker
  // Each CATCH-PUSH records a list of all the exception id and handler label
  // pairs handled for its exact block

  // Gather all try-catch blocks that have cur_pc as the starting pc
  typedef std::vector<std::reference_wrapper<
    const java_bytecode_convert_methodt::methodt::exceptiont>> exceptionst;
  std::map<std::size_t, exceptionst> exceptions_by_end;
  for(const java_bytecode_convert_methodt::methodt::exceptiont &exception
    : method.exception_table)
  {
    if(exception.start_pc == cur_pc)
      exceptions_by_end[exception.end_pc].push_back(exception);
  }
  for(const auto &exceptions : exceptions_by_end)
  {
    // For each block with a distinct end position create one CATCH-PUSH
    code_push_catcht catch_push;
    // Fill in its exception_list
    code_push_catcht::exception_listt &exception_list =
      catch_push.exception_list();
    for(const java_bytecode_convert_methodt::methodt::exceptiont &exception
      : exceptions.second)
    {
      exception_list.emplace_back(
        exception.catch_type.get_identifier(),
        // Record the exception handler in the CATCH-PUSH instruction by
        // generating a label corresponding to the handler's pc
        label(std::to_string(exception.handler_pc)));
    }
    // Prepend the CATCH-PUSH instruction
    code = code_blockt({ std::move(catch_push), code });
  }

  // Next add the CATCH-POP instructions
  // exception_row.end_pc is exclusive so append a CATCH-POP instruction if
  // this is the instruction before it.
  // To do this, attempt to find all exception handlers that end at the
  // earliest known instruction after this one.

  // Dangerously, we assume that the next opcode in the bytecode after the end
  // of the exception handler block (whose address matches the exclusive end
  // position of the block) will be a successor of some code investigated
  // before the instruction at the end of that handler and therefore in the
  // working set.
  // As an example of where this may fail, for non-obfuscated bytecode
  // generated by most compilers the next opcode after the block ending at the
  // end of the try block is the lexically next bit of code after the try
  // block, i.e. the catch block. When there aren't any throwing statements in
  // the try block this block will not be the successor of any instruction.

  auto next_opcode_it = std::find_if(
    working_set.begin(),
    working_set.end(),
    [cur_pc](method_offsett offset) { return offset > cur_pc; });
  if(next_opcode_it != working_set.end())
  {
    // Count the distinct start positions of handlers that end at this location
    std::set<std::size_t> start_positions;  // Use a set to deduplicate
    for(const auto &exception_row : method.exception_table)
    {
      // Check if the next instruction found is the (exclusive) end of a block
      if(*next_opcode_it == exception_row.end_pc)
        start_positions.insert(exception_row.start_pc);
    }
    for(std::size_t handler = 0; handler < start_positions.size(); ++handler)
    {
      // Append a CATCH-POP instruction before the end of the block
      code = code_blockt({ code, code_pop_catcht() });
    }
  }

  return code;
}

code_blockt java_bytecode_convert_methodt::convert_multianewarray(
  const source_locationt &location,
  const exprt &arg0,
  const exprt::operandst &op,
  exprt::operandst &results)
{
  const reference_typet ref_type = java_reference_type(arg0.type());
  side_effect_exprt java_new_array(ID_java_new_array, ref_type, location);
  java_new_array.operands() = op;

  code_blockt create;

  if(max_array_length != 0)
  {
    constant_exprt size_limit = from_integer(max_array_length, java_int_type());
    binary_relation_exprt le_max_size(op[0], ID_le, size_limit);
    code_assumet assume_le_max_size(le_max_size);
    create.add(assume_le_max_size);
  }

  const exprt tmp = tmp_variable("newarray", ref_type);
  create.add(code_assignt(tmp, java_new_array));
  results[0] = tmp;

  return create;
}

code_blockt java_bytecode_convert_methodt::convert_newarray(
  const source_locationt &location,
  const irep_idt &statement,
  const exprt &arg0,
  const exprt::operandst &op,
  exprt::operandst &results)
{
  java_reference_typet ref_type = [&]() {
    if(statement == "newarray")
    {
      irep_idt id = arg0.type().id();

      char element_type;
      if(id == ID_bool)
        element_type = 'z';
      else if(id == ID_char)
        element_type = 'c';
      else if(id == ID_float)
        element_type = 'f';
      else if(id == ID_double)
        element_type = 'd';
      else if(id == ID_byte)
        element_type = 'b';
      else if(id == ID_short)
        element_type = 's';
      else if(id == ID_int)
        element_type = 'i';
      else if(id == ID_long)
        element_type = 'j';
      else
        element_type = '?';
      return java_array_type(element_type);
    }
    else
    {
      return java_reference_array_type(to_struct_tag_type(arg0.type()));
    }
  }();

  side_effect_exprt java_new_array(ID_java_new_array, ref_type, location);
  java_new_array.copy_to_operands(op[0]);

  code_blockt block;

  if(max_array_length != 0)
  {
    constant_exprt size_limit = from_integer(max_array_length, java_int_type());
    binary_relation_exprt le_max_size(op[0], ID_le, size_limit);
    code_assumet assume_le_max_size(le_max_size);
    block.add(std::move(assume_le_max_size));
  }
  const exprt tmp = tmp_variable("newarray", ref_type);
  block.add(code_assignt(tmp, java_new_array));
  results[0] = tmp;

  return block;
}

void java_bytecode_convert_methodt::convert_new(
  const source_locationt &location,
  const exprt &arg0,
  codet &c,
  exprt::operandst &results)
{
  const reference_typet ref_type = java_reference_type(arg0.type());
  side_effect_exprt java_new_expr(ID_java_new, ref_type, location);

  if(!location.get_line().empty())
    java_new_expr.add_source_location() = location;

  const exprt tmp = tmp_variable("new", ref_type);
  c = code_assignt(tmp, java_new_expr);
  c.add_source_location() = location;
  codet clinit_call =
    get_clinit_call(to_struct_tag_type(arg0.type()).get_identifier());
  if(clinit_call.get_statement() != ID_skip)
  {
    c = code_blockt({clinit_call, c});
  }
  results[0] = tmp;
}

code_blockt java_bytecode_convert_methodt::convert_putstatic(
  const source_locationt &location,
  const exprt &arg0,
  const exprt::operandst &op,
  const symbol_exprt &symbol_expr)
{
  if(needed_lazy_methods && arg0.type().id() == ID_struct_tag)
  {
    needed_lazy_methods->add_needed_class(
      to_struct_tag_type(arg0.type()).get_identifier());
  }

  code_blockt block;
  block.add_source_location() = location;

  // Note this initializer call deliberately inits the class used to make
  // the reference, which may be a child of the class that actually defines
  // the field.
  codet clinit_call = get_clinit_call(arg0.get_string(ID_class));
  if(clinit_call.get_statement() != ID_skip)
    block.add(clinit_call);

  save_stack_entries(
    "stack_static_field",
    block,
    bytecode_write_typet::STATIC_FIELD,
    symbol_expr.get_identifier());
  block.add(code_assignt(symbol_expr, op[0]));
  return block;
}

code_blockt java_bytecode_convert_methodt::convert_putfield(
  const fieldref_exprt &arg0,
  const exprt::operandst &op)
{
  code_blockt block;
  save_stack_entries(
    "stack_field", block, bytecode_write_typet::FIELD, arg0.component_name());
  block.add(code_assignt(to_member(op[0], arg0, ns), op[1]));
  return block;
}

void java_bytecode_convert_methodt::convert_getstatic(
  const source_locationt &source_location,
  const exprt &arg0,
  const symbol_exprt &symbol_expr,
  const bool is_assertions_disabled_field,
  codet &c,
  exprt::operandst &results)
{
  if(needed_lazy_methods)
  {
    if(arg0.type().id() == ID_struct_tag)
    {
      needed_lazy_methods->add_needed_class(
        to_struct_tag_type(arg0.type()).get_identifier());
    }
    else if(arg0.type().id() == ID_pointer)
    {
      const auto &pointer_type = to_pointer_type(arg0.type());
      if(pointer_type.subtype().id() == ID_struct_tag)
      {
        needed_lazy_methods->add_needed_class(
          to_struct_tag_type(pointer_type.subtype()).get_identifier());
      }
    }
    else if(is_assertions_disabled_field)
    {
      needed_lazy_methods->add_needed_class(arg0.get_string(ID_class));
    }
  }
  symbol_exprt symbol_with_location = symbol_expr;
  symbol_with_location.add_source_location() = source_location;
  results[0] = java_bytecode_promotion(symbol_with_location);

  // Note this initializer call deliberately inits the class used to make
  // the reference, which may be a child of the class that actually defines
  // the field.
  codet clinit_call = get_clinit_call(arg0.get_string(ID_class));
  if(clinit_call.get_statement() != ID_skip)
    c = clinit_call;
  else if(is_assertions_disabled_field)
  {
    // set $assertionDisabled to false
    c = code_assignt(symbol_expr, false_exprt());
  }
}

exprt::operandst &java_bytecode_convert_methodt::convert_cmp2(
  const irep_idt &statement,
  const exprt::operandst &op,
  exprt::operandst &results) const
{
  const int nan_value(statement[4] == 'l' ? -1 : 1);
  const typet result_type(java_int_type());
  const exprt nan_result(from_integer(nan_value, result_type));

  // (value1 == NaN || value2 == NaN) ?
  //   nan_value : value1  < value2 ? -1 : value2 < value1  1 ? 1 : 0;
  // (value1 == NaN || value2 == NaN) ?
  //   nan_value : value1 == value2 ? 0  : value1 < value2 -1 ? 1 : 0;

  isnan_exprt nan_op0(op[0]);
  isnan_exprt nan_op1(op[1]);
  exprt one = from_integer(1, result_type);
  exprt minus_one = from_integer(-1, result_type);
  results[0] = if_exprt(
    or_exprt(nan_op0, nan_op1),
    nan_result,
    if_exprt(
      ieee_float_equal_exprt(op[0], op[1]),
      from_integer(0, result_type),
      if_exprt(binary_relation_exprt(op[0], ID_lt, op[1]), minus_one, one)));
  return results;
}

exprt::operandst &java_bytecode_convert_methodt::convert_cmp(
  const exprt::operandst &op,
  exprt::operandst &results) const
{ // The integer result on the stack is:
  //  0 if op[0] equals op[1]
  // -1 if op[0] is less than op[1]
  //  1 if op[0] is greater than op[1]

  const typet t = java_int_type();
  exprt one = from_integer(1, t);
  exprt minus_one = from_integer(-1, t);

  if_exprt greater =
    if_exprt(binary_relation_exprt(op[0], ID_gt, op[1]), one, minus_one);

  results[0] = if_exprt(
    binary_relation_exprt(op[0], ID_equal, op[1]), from_integer(0, t), greater);
  return results;
}

exprt::operandst &java_bytecode_convert_methodt::convert_shl(
  const irep_idt &statement,
  const exprt::operandst &op,
  exprt::operandst &results) const
{
  const typet type = java_type_from_char(statement[0]);

  const std::size_t width = get_bytecode_type_width(type);

  // According to JLS 15.19 Shift Operators
  // a mask 0b11111 is applied for int and 0b111111 for long.
  exprt mask = from_integer(width - 1, op[1].type());

  results[0] = shl_exprt(op[0], bitand_exprt(op[1], mask));
  return results;
}

exprt::operandst &java_bytecode_convert_methodt::convert_ushr(
  const irep_idt &statement,
  const exprt::operandst &op,
  exprt::operandst &results) const
{
  const typet type = java_type_from_char(statement[0]);

  const std::size_t width = get_bytecode_type_width(type);
  typet target = unsignedbv_typet(width);

  exprt lhs = typecast_exprt::conditional_cast(op[0], target);
  exprt rhs = typecast_exprt::conditional_cast(op[1], target);

  results[0] =
    typecast_exprt::conditional_cast(lshr_exprt(lhs, rhs), op[0].type());

  return results;
}

code_blockt java_bytecode_convert_methodt::convert_iinc(
  const exprt &arg0,
  const exprt &arg1,
  const source_locationt &location,
  const method_offsett address)
{
  code_blockt block;
  block.add_source_location() = location;
  // search variable on stack
  const exprt &locvar = variable(arg0, 'i', address);
  save_stack_entries(
    "stack_iinc",
    block,
    bytecode_write_typet::VARIABLE,
    to_symbol_expr(locvar).get_identifier());

  const exprt arg1_int_type =
    typecast_exprt::conditional_cast(arg1, java_int_type());
  code_assignt code_assign(
    variable(arg0, 'i', address),
    plus_exprt(
      typecast_exprt::conditional_cast(
        variable(arg0, 'i', address), java_int_type()),
      arg1_int_type));
  block.add(std::move(code_assign));

  return block;
}

code_ifthenelset java_bytecode_convert_methodt::convert_ifnull(
  const java_bytecode_convert_methodt::address_mapt &address_map,
  const exprt::operandst &op,
  const mp_integer &number,
  const source_locationt &location) const
{
  const typecast_exprt lhs(op[0], java_reference_type(java_void_type()));
  const exprt rhs(null_pointer_exprt(to_pointer_type(lhs.type())));

  const method_offsett label_number = numeric_cast_v<method_offsett>(number);

  code_ifthenelset code_branch(
    binary_relation_exprt(lhs, ID_equal, rhs),
    code_gotot(label(std::to_string(label_number))));

  code_branch.then_case().add_source_location() =
    address_map.at(label_number).source->source_location;
  code_branch.add_source_location() = location;

  return code_branch;
}

code_ifthenelset java_bytecode_convert_methodt::convert_ifnonull(
  const java_bytecode_convert_methodt::address_mapt &address_map,
  const exprt::operandst &op,
  const mp_integer &number,
  const source_locationt &location) const
{
  const typecast_exprt lhs(op[0], java_reference_type(java_void_type()));
  const exprt rhs(null_pointer_exprt(to_pointer_type(lhs.type())));

  const method_offsett label_number = numeric_cast_v<method_offsett>(number);

  code_ifthenelset code_branch(
    binary_relation_exprt(lhs, ID_notequal, rhs),
    code_gotot(label(std::to_string(label_number))));

  code_branch.then_case().add_source_location() =
    address_map.at(label_number).source->source_location;
  code_branch.add_source_location() = location;

  return code_branch;
}

code_ifthenelset java_bytecode_convert_methodt::convert_if(
  const java_bytecode_convert_methodt::address_mapt &address_map,
  const exprt::operandst &op,
  const irep_idt &id,
  const mp_integer &number,
  const source_locationt &location) const
{
  const method_offsett label_number = numeric_cast_v<method_offsett>(number);

  code_ifthenelset code_branch(
    binary_relation_exprt(op[0], id, from_integer(0, op[0].type())),
    code_gotot(label(std::to_string(label_number))));

  code_branch.cond().add_source_location() = location;
  code_branch.cond().add_source_location().set_function(method_id);
  code_branch.then_case().add_source_location() =
    address_map.at(label_number).source->source_location;
  code_branch.then_case().add_source_location().set_function(method_id);
  code_branch.add_source_location() = location;
  code_branch.add_source_location().set_function(method_id);

  return code_branch;
}

code_ifthenelset java_bytecode_convert_methodt::convert_if_cmp(
  const java_bytecode_convert_methodt::address_mapt &address_map,
  const u1 bytecode,
  const exprt::operandst &op,
  const mp_integer &number,
  const source_locationt &location) const
{
  const irep_idt cmp_op = get_if_cmp_operator(bytecode);
  binary_relation_exprt condition(
    op[0], cmp_op, typecast_exprt::conditional_cast(op[1], op[0].type()));
  condition.add_source_location() = location;

  const method_offsett label_number = numeric_cast_v<method_offsett>(number);

  code_ifthenelset code_branch(
    std::move(condition), code_gotot(label(std::to_string(label_number))));

  code_branch.then_case().add_source_location() =
    address_map.at(label_number).source->source_location;
  code_branch.add_source_location() = location;

  return code_branch;
}

code_blockt java_bytecode_convert_methodt::convert_ret(
  const std::vector<method_offsett> &jsr_ret_targets,
  const exprt &arg0,
  const source_locationt &location,
  const method_offsett address)
{
  code_blockt c;
  auto retvar = variable(arg0, 'a', address);
  for(size_t idx = 0, idxlim = jsr_ret_targets.size(); idx != idxlim; ++idx)
  {
    irep_idt number = std::to_string(jsr_ret_targets[idx]);
    code_gotot g(label(number));
    g.add_source_location() = location;
    if(idx == idxlim - 1)
      c.add(g);
    else
    {
      auto address_ptr =
        from_integer(jsr_ret_targets[idx], unsignedbv_typet(64));
      address_ptr.type() = pointer_type(java_void_type());

      code_ifthenelset branch(equal_exprt(retvar, address_ptr), std::move(g));

      branch.cond().add_source_location() = location;
      branch.add_source_location() = location;

      c.add(std::move(branch));
    }
  }
  return c;
}

/// Add typecast if necessary to \p expr to make it compatible with array type
/// corresponding to \p type_char (see \ref java_array_type(const char)).
/// Character 'b' is used both for `byte` and `boolean` arrays, so if \p expr
/// is a boolean array and we are using a `b` operation we can skip the
/// typecast.
static exprt conditional_array_cast(const exprt &expr, char type_char)
{
  const auto ref_type =
    type_try_dynamic_cast<java_reference_typet>(expr.type());
  const bool typecast_not_needed =
    ref_type && ((type_char == 'b' && ref_type->subtype().get_identifier() ==
                                        "java::array[boolean]") ||
                 *ref_type == java_array_type(type_char));
  return typecast_not_needed ? expr
                             : typecast_exprt(expr, java_array_type(type_char));
}

exprt java_bytecode_convert_methodt::convert_aload(
  const irep_idt &statement,
  const exprt::operandst &op)
{
  PRECONDITION(op.size() == 2);
  const char type_char = statement[0];
  const exprt op_with_right_type = conditional_array_cast(op[0], type_char);
  dereference_exprt deref{op_with_right_type};
  deref.set(ID_java_member_access, true);

  auto java_array_type = type_try_dynamic_cast<struct_tag_typet>(deref.type());
  INVARIANT(java_array_type, "Java array type should be a struct_tag_typet");
  member_exprt data_ptr{
    deref, "data", pointer_type(java_array_element_type(*java_array_type))};
  plus_exprt data_plus_offset{std::move(data_ptr), op[1]};
  // tag it so it's easy to identify during instrumentation
  data_plus_offset.set(ID_java_array_access, true);
  return java_bytecode_promotion(dereference_exprt{data_plus_offset});
}

exprt java_bytecode_convert_methodt::convert_load(
  const exprt &index,
  char type_char,
  size_t address)
{
  const exprt var = variable(index, type_char, address);
  if(type_char == 'i')
  {
    INVARIANT(
      can_cast_type<bitvector_typet>(var.type()) &&
        type_try_dynamic_cast<bitvector_typet>(var.type())->get_width() <= 32,
      "iload can be used for boolean, byte, short, int and char");
    return typecast_exprt::conditional_cast(var, java_int_type());
  }
  INVARIANT(
    (type_char == 'a' && can_cast_type<reference_typet>(var.type())) ||
      var.type() == java_type_from_char(type_char),
    "Variable type must match [adflv]load return type");
  return var;
}

code_blockt java_bytecode_convert_methodt::convert_store(
  const irep_idt &statement,
  const exprt &arg0,
  const exprt::operandst &op,
  const method_offsett address,
  const source_locationt &location)
{
  const exprt var = variable(arg0, statement[0], address);
  const irep_idt &var_name = to_symbol_expr(var).get_identifier();

  code_blockt block;
  block.add_source_location() = location;

  save_stack_entries(
    "stack_store",
    block,
    bytecode_write_typet::VARIABLE,
    var_name);

  block.add(
    code_assignt{var, typecast_exprt::conditional_cast(op[0], var.type())},
    location);
  return block;
}

code_blockt java_bytecode_convert_methodt::convert_astore(
  const irep_idt &statement,
  const exprt::operandst &op,
  const source_locationt &location)
{
  PRECONDITION(op.size() == 3);
  const char type_char = statement[0];
  const exprt op_with_right_type = conditional_array_cast(op[0], type_char);
  dereference_exprt deref{op_with_right_type};
  deref.set(ID_java_member_access, true);

  auto java_array_type = type_try_dynamic_cast<struct_tag_typet>(deref.type());
  INVARIANT(java_array_type, "Java array type should be a struct_tag_typet");
  member_exprt data_ptr{
    deref, "data", pointer_type(java_array_element_type(*java_array_type))};
  plus_exprt data_plus_offset{std::move(data_ptr), op[1]};
  // tag it so it's easy to identify during instrumentation
  data_plus_offset.set(ID_java_array_access, true);

  code_blockt block;
  block.add_source_location() = location;

  save_stack_entries(
    "stack_astore", block, bytecode_write_typet::ARRAY_REF, "");

  code_assignt array_put{dereference_exprt{data_plus_offset}, op[2]};
  block.add(std::move(array_put), location);
  return block;
}

optionalt<exprt> java_bytecode_convert_methodt::convert_invoke_dynamic(
  const source_locationt &location,
  std::size_t instruction_address,
  const exprt &arg0,
  codet &result_code)
{
  const java_method_typet &method_type = to_java_method_type(arg0.type());
  const java_method_typet::parameterst &parameters(method_type.parameters());
  const typet &return_type = method_type.return_type();

  // Note these must be popped regardless of whether we understand the lambda
  // method or not
  code_function_callt::argumentst arguments = pop(parameters.size());

  irep_idt synthetic_class_name =
    lambda_synthetic_class_name(method_id, instruction_address);

  if(!symbol_table.has_symbol(synthetic_class_name))
  {
    // We failed to parse the invokedynamic handle as a Java 8+ lambda;
    // give up and return null.
    const auto value = zero_initializer(return_type, location, ns);
    if(!value.has_value())
    {
      log.error().source_location = location;
      log.error() << "failed to zero-initialize return type" << messaget::eom;
      throw 0;
    }
    return value;
  }

  // Construct an instance of the synthetic class created for this invokedynamic
  // site:

  irep_idt constructor_name = id2string(synthetic_class_name) + ".<init>";

  const symbolt &constructor_symbol = ns.lookup(constructor_name);

  code_blockt result;

  // SyntheticType lambda_new = new SyntheticType;
  const reference_typet ref_type =
    java_reference_type(struct_tag_typet(synthetic_class_name));
  side_effect_exprt java_new_expr(ID_java_new, ref_type, location);
  const exprt new_instance = tmp_variable("lambda_new", ref_type);
  result.add(code_assignt(new_instance, java_new_expr, location));

  // lambda_new.<init>(capture_1, capture_2, ...);
  // Add the implicit 'this' parameter:
  arguments.insert(arguments.begin(), new_instance);
  adjust_invoke_argument_types(
    to_code_type(constructor_symbol.type).parameters(), arguments);

  code_function_callt constructor_call(
    constructor_symbol.symbol_expr(), arguments);
  constructor_call.add_source_location() = location;
  result.add(constructor_call);
  if(needed_lazy_methods)
  {
    needed_lazy_methods->add_needed_method(constructor_symbol.name);
    needed_lazy_methods->add_needed_class(synthetic_class_name);
  }

  result_code = std::move(result);

  if(return_type.id() == ID_empty)
    return {};
  else
    return new_instance;
}

void java_bytecode_convert_methodt::draw_edges_from_ret_to_jsr(
  java_bytecode_convert_methodt::address_mapt &address_map,
  const std::vector<method_offsett> &jsr_ret_targets,
  const std::vector<
    std::vector<java_bytecode_parse_treet::instructiont>::const_iterator>
    &ret_instructions) const
{ // Draw edges from every `ret` to every `jsr` successor. Could do better with
  // flow analysis to distinguish multiple subroutines within the same function.
  for(const auto &retinst : ret_instructions)
  {
    auto &a_entry = address_map.at(retinst->address);
    a_entry.successors.insert(
      a_entry.successors.end(), jsr_ret_targets.begin(), jsr_ret_targets.end());
  }
}

std::vector<java_bytecode_convert_methodt::method_offsett>
java_bytecode_convert_methodt::try_catch_handler(
  const method_offsett address,
  const java_bytecode_parse_treet::methodt::exception_tablet &exception_table)
  const
{
  std::vector<method_offsett> result;
  for(const auto &exception_row : exception_table)
  {
    if(address >= exception_row.start_pc && address < exception_row.end_pc)
      result.push_back(exception_row.handler_pc);
  }
  return result;
}

/// This uses a cut-down version of the logic in
/// java_bytecode_convert_methodt::convert to initialize symbols for the
/// parameters and update the parameters in the type of method_symbol with
/// names read from the local_variable_table read from the bytecode
/// \remarks This is useful for pre-initialization for methods generated by
/// the string solver
/// \param method_symbol: The symbol for the method for which to initialize the
///   parameters
/// \param local_variable_table: The local variable table containing the
///   bytecode for the parameters
/// \param symbol_table: The symbol table into which to insert symbols for the
///   parameters
void java_bytecode_initialize_parameter_names(
  symbolt &method_symbol,
  const java_bytecode_parse_treet::methodt::local_variable_tablet
    &local_variable_table,
  symbol_table_baset &symbol_table)
{
  // Obtain a std::vector of java_method_typet::parametert objects from the
  // (function) type of the symbol
  java_method_typet &method_type = to_java_method_type(method_symbol.type);
  java_method_typet::parameterst &parameters = method_type.parameters();

  // Find number of parameters
  unsigned slots_for_parameters = java_method_parameter_slots(method_type);

  // Find parameter names in the local variable table:
  typedef std::pair<irep_idt, irep_idt> base_name_and_identifiert;
  std::map<std::size_t, base_name_and_identifiert> param_names;
  for(const auto &v : local_variable_table)
  {
    if(v.index < slots_for_parameters)
      param_names.emplace(
        v.index,
        make_pair(
          v.name, id2string(method_symbol.name) + "::" + id2string(v.name)));
  }

  // Assign names to parameters
  std::size_t param_index = 0;
  for(auto &param : parameters)
  {
    irep_idt base_name, identifier;

    // Construct a sensible base name (base_name) and a fully qualified name
    // (identifier) for every parameter of the method under translation,
    // regardless of whether we have an LVT or not; and assign it to the
    // parameter object (which is stored in the type of the symbol, not in the
    // symbol table)
    if(param_index == 0 && param.get_this())
    {
      // my.package.ClassName.myMethodName:(II)I::this
      base_name = ID_this;
      identifier = id2string(method_symbol.name) + "::" + id2string(base_name);
    }
    else
    {
      auto param_name = param_names.find(param_index);
      if(param_name != param_names.end())
      {
        base_name = param_name->second.first;
        identifier = param_name->second.second;
      }
      else
      {
        // my.package.ClassName.myMethodName:(II)I::argNT, where N is the local
        // variable slot where the parameter is stored and T is a character
        // indicating the type
        const typet &type = param.type();
        char suffix = java_char_from_type(type);
        base_name = "arg" + std::to_string(param_index) + suffix;
        identifier =
          id2string(method_symbol.name) + "::" + id2string(base_name);
      }
    }
    param.set_base_name(base_name);
    param.set_identifier(identifier);

    // Build a new symbol for the parameter and add it to the symbol table
    parameter_symbolt parameter_symbol;
    parameter_symbol.base_name = base_name;
    parameter_symbol.mode = ID_java;
    parameter_symbol.name = identifier;
    parameter_symbol.type = param.type();
    symbol_table.insert(parameter_symbol);

    param_index += java_local_variable_slots(param.type());
  }
}

void java_bytecode_convert_method(
  const symbolt &class_symbol,
  const java_bytecode_parse_treet::methodt &method,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  bool throw_assertion_error,
  optionalt<ci_lazy_methods_neededt> needed_lazy_methods,
  java_string_library_preprocesst &string_preprocess,
  const class_hierarchyt &class_hierarchy,
  bool threading_support,
  const optionalt<prefix_filtert> &method_context,
  bool assert_no_exceptions_thrown)

{
  java_bytecode_convert_methodt java_bytecode_convert_method(
    symbol_table,
    message_handler,
    max_array_length,
    throw_assertion_error,
    needed_lazy_methods,
    string_preprocess,
    class_hierarchy,
    threading_support,
    assert_no_exceptions_thrown);

  java_bytecode_convert_method(class_symbol, method, method_context);
}

/// Returns true iff method \p methodid from class \p classname is
/// a method inherited from a class or interface from which
/// \p classname inherits, either directly or indirectly.
/// \param classname: class whose method is referenced
/// \param mangled_method_name: The particular overload of a given method.
bool java_bytecode_convert_methodt::is_method_inherited(
  const irep_idt &classname,
  const irep_idt &mangled_method_name) const
{
  const auto inherited_method = get_inherited_method_implementation(
    mangled_method_name, classname, symbol_table);

  return inherited_method.has_value();
}

/// Get static field identifier referred to by `class_identifier.component_name`
/// Note this may be inherited from either a parent or an interface.
/// \param class_identifier: class used to refer to the field
/// \param component_name: component (static field) name
/// \return identifier of the actual concrete field referred to
irep_idt java_bytecode_convert_methodt::get_static_field(
  const irep_idt &class_identifier,
  const irep_idt &component_name) const
{
  const auto inherited_method = get_inherited_component(
    class_identifier, component_name, symbol_table, true);

  INVARIANT(
    inherited_method.has_value(), "static field should be in symbol table");

  return inherited_method->get_full_component_identifier();
}

/// Create temporary variables if a write instruction can have undesired side-
/// effects.
/// \param tmp_var_prefix: The prefix string to use for new temporary variables
/// \param [out] block: The code block the assignment is added to if required.
/// \param write_type: The enumeration type of the write instruction.
/// \param identifier: The identifier of the symbol in the write instruction.
void java_bytecode_convert_methodt::save_stack_entries(
  const std::string &tmp_var_prefix,
  code_blockt &block,
  const bytecode_write_typet write_type,
  const irep_idt &identifier)
{
  const std::function<bool(
    const std::function<tvt(const exprt &expr)>, const exprt &expr)>
    entry_matches = [&entry_matches](
      const std::function<tvt(const exprt &expr)> predicate,
      const exprt &expr) {
      const tvt &tvres = predicate(expr);
      if(tvres.is_unknown())
      {
        return std::any_of(
          expr.operands().begin(),
          expr.operands().end(),
          [&predicate, &entry_matches](const exprt &expr) {
            return entry_matches(predicate, expr);
          });
      }
      else
      {
        return tvres.is_true();
      }
    };

  // Function that checks whether the expression accesses a member with the
  // given identifier name. These accesses are created in the case of `iinc`, or
  // non-array `?store` instructions.
  const std::function<tvt(const exprt &expr)> has_member_entry = [&identifier](
    const exprt &expr) {
    const auto member_expr = expr_try_dynamic_cast<member_exprt>(expr);
    return !member_expr ? tvt::unknown()
                        : tvt(member_expr->get_component_name() == identifier);
  };

  // Function that checks whether the expression is a symbol with the given
  // identifier name. These accesses are created in the case of `putstatic` or
  // `putfield` instructions.
  const std::function<tvt(const exprt &expr)> is_symbol_entry =
    [&identifier](const exprt &expr) {
      const auto symbol_expr = expr_try_dynamic_cast<symbol_exprt>(expr);
      return !symbol_expr ? tvt::unknown()
                          : tvt(symbol_expr->get_identifier() == identifier);
    };

  // Function that checks whether the expression is a dereference
  // expression. These accesses are created in `?astore` array write
  // instructions.
  const std::function<tvt(const exprt &expr)> is_dereference_entry =
    [](const exprt &expr) {
      const auto dereference_expr =
        expr_try_dynamic_cast<dereference_exprt>(expr);
      return !dereference_expr ? tvt::unknown() : tvt(true);
    };

  for(auto &stack_entry : stack)
  {
    bool replace = false;
    switch(write_type)
    {
    case bytecode_write_typet::VARIABLE:
    case bytecode_write_typet::STATIC_FIELD:
      replace = entry_matches(is_symbol_entry, stack_entry);
      break;
    case bytecode_write_typet::ARRAY_REF:
      replace = entry_matches(is_dereference_entry, stack_entry);
      break;
    case bytecode_write_typet::FIELD:
      replace = entry_matches(has_member_entry, stack_entry);
      break;
    }
    if(replace)
    {
      create_stack_tmp_var(
          tmp_var_prefix, stack_entry.type(), block, stack_entry);
    }
  }
}

/// actually create a temporary variable to hold the value of a stack entry
void java_bytecode_convert_methodt::create_stack_tmp_var(
  const std::string &tmp_var_prefix,
  const typet &tmp_var_type,
  code_blockt &block,
  exprt &stack_entry)
{
  const exprt tmp_var=
    tmp_variable(tmp_var_prefix, tmp_var_type);
  block.add(code_assignt(tmp_var, stack_entry));
  stack_entry=tmp_var;
}

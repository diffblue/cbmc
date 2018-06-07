/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Language Conversion

#ifdef DEBUG
#include <iostream>
#endif

#include "java_bytecode_convert_method.h"
#include "java_bytecode_convert_method_class.h"
#include "bytecode_info.h"
#include "java_static_initializers.h"
#include "java_string_library_preprocess.h"
#include "java_types.h"
#include "java_utils.h"
#include "remove_exceptions.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string2int.h>
#include <util/string_constant.h>
#include <util/threeval.h>

#include <goto-programs/cfg.h>
#include <goto-programs/class_hierarchy.h>
#include <goto-programs/resolve_inherited_component.h>

#include <analyses/cfg_dominators.h>
#include <analyses/uncaught_exceptions_analysis.h>

#include <limits>
#include <algorithm>
#include <functional>
#include <unordered_set>
#include <regex>

/// Given a string of the format '?blah?', will return true when compared
/// against a string that matches appart from any characters that are '?'
/// in the original string. Equivalent to doing a regex match on '.blah.'
class patternt
{
public:
  explicit patternt(const char *_p):p(_p)
  {
  }

  // match with '?'
  bool operator==(const irep_idt &what) const
  {
    for(std::size_t i=0; i<what.size(); i++)
      if(p[i]==0)
        return false;
      else if(p[i]!='?' && p[i]!=what[i])
        return false;

    return p[what.size()]==0;
  }

protected:
  const char *p;
};

/// Iterates through the parameters of the function type \p ftype, finds a new
/// new name for each parameter and renames them in `ftype.parameters()` as
/// well as in the \p symbol_table.
/// \param[in,out] ftype:
///   Function type whose parameters should be named.
/// \param name_prefix:
///   Prefix for parameter names, typically the parent function's name.
/// \param[in,out] symbol_table:
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
      base_name="this";
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

static bool operator==(const irep_idt &what, const patternt &pattern)
{
  return pattern==what;
}

static bool is_constructor(const irep_idt &method_name)
{
  return id2string(method_name).find("<init>") != std::string::npos;
}

exprt::operandst java_bytecode_convert_methodt::pop(std::size_t n)
{
  if(stack.size()<n)
  {
    error() << "malformed bytecode (pop too high)" << eom;
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

/// Returns a symbol_exprt indicating a local variable suitable to load/store
/// from a bytecode at address `address` a value of type `type_char` stored in
/// the JVM's slot `arg`.
///
/// \param arg
///   The local variable slot
/// \param type_char
///   The type of the value stored in the slot pointed by `arg`.
/// \param address
///   Bytecode address used to find a variable that the LVT declares to be live
///   and living in the slot pointed by `arg` for this bytecode.
/// \param do_cast
///   Indicates whether we should return the original symbol_exprt or a
///   typecast_exprt if the type of the symbol_exprt does not equal that
///   represented by `type_char`.
const exprt java_bytecode_convert_methodt::variable(
  const exprt &arg,
  char type_char,
  size_t address,
  java_bytecode_convert_methodt::variable_cast_argumentt do_cast)
{
  mp_integer number;
  bool ret=to_integer(to_constant_expr(arg), number);
  CHECK_RETURN(!ret);

  std::size_t number_int=integer2size_t(number);
  typet t=java_type_from_char(type_char);
  variablest &var_list=variables[number_int];

  // search variable in list for correct frame / address if necessary
  const variablet &var=
    find_variable_for_slot(address, var_list);

  if(var.symbol_expr.get_identifier().empty())
  {
    // an unnamed local variable
    irep_idt base_name="anonlocal::"+std::to_string(number_int)+type_char;
    irep_idt identifier=id2string(current_method)+"::"+id2string(base_name);

    symbol_exprt result(identifier, t);
    result.set(ID_C_base_name, base_name);
    used_local_names.insert(result);
    return result;
  }
  else
  {
    exprt result=var.symbol_expr;
    if(do_cast==CAST_AS_NEEDED && t!=result.type())
      result=typecast_exprt(result, t);
    return result;
  }
}

/// Returns the member type for a method, based on signature or descriptor
/// \param descriptor
///   descriptor of the method
/// \param signature
///   signature of the method
/// \param class_name
///   string containing the name of the corresponding class
/// \param method_name
///   string containing the name of the method
/// \param message_handler
///   message handler to collect warnings
/// \return
///   the constructed member type
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

  typet member_type_from_descriptor=java_type_from_string(descriptor);
  INVARIANT(member_type_from_descriptor.id()==ID_code, "Must be code type");
  if(signature.has_value())
  {
    try
    {
      typet member_type_from_signature=java_type_from_string(
        signature.value(),
        class_name);
      INVARIANT(member_type_from_signature.id()==ID_code, "Must be code type");
      if(
        to_java_method_type(member_type_from_signature).parameters().size() ==
        to_java_method_type(member_type_from_descriptor).parameters().size())
      {
        return to_java_method_type(member_type_from_signature);
      }
      else
      {
        message.warning() << "Method: " << class_name << "." << method_name
                          << "\n signature: " << signature.value()
                          << "\n descriptor: " << descriptor
                          << "\n different number of parameters, reverting to "
                             "descriptor"
                          << message.eom;
      }
    }
    catch(const unsupported_java_class_signature_exceptiont &e)
    {
      message.warning() << "Method: " << class_name << "." << method_name
                        << "\n could not parse signature: " << signature.value()
                        << "\n " << e.what() << "\n"
                        << " reverting to descriptor: " << descriptor
                        << message.eom;
    }
  }
  return to_java_method_type(member_type_from_descriptor);
}

/// Retrieves the symbol of the lambda method associated with the given
/// lambda method handle (bootstrap method).
/// \param lambda_method_handles Vector of lambda method handles (bootstrap
///   methods) of the class where the lambda is called
/// \param index Index of the lambda method handle in the vector
/// \return Symbol of the lambda method if the method handle has a known type
optionalt<symbolt> java_bytecode_convert_methodt::get_lambda_method_symbol(
  const java_class_typet::java_lambda_method_handlest &lambda_method_handles,
  const size_t index)
{
  const symbol_exprt &lambda_method_handle = lambda_method_handles.at(index);
  // If the lambda method handle has an unknown type, it does not refer to
  // any symbol (it is a symbol expression with empty identifier)
  if(!lambda_method_handle.get_identifier().empty())
    return symbol_table.lookup_ref(lambda_method_handle.get_identifier());
  return {};
}

/// This creates a method symbol in the symtab, but doesn't actually perform
/// method conversion just yet. The caller should call
/// java_bytecode_convert_method later to give the symbol/method a body.
/// \par parameters: `class_symbol`: class this method belongs to
/// `method_identifier`: fully qualified method name, including type descriptor
///   (e.g. "x.y.z.f:(I)")
/// `m`: parsed method object to convert
/// `symbol_table`: global symbol table (will be modified)
/// `message_handler`: message handler to collect warnings
void java_bytecode_convert_method_lazy(
  const symbolt &class_symbol,
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

  if(m.is_bridge)
    member_type.set(ID_is_bridge_method, m.is_bridge);

  // do we need to add 'this' as a parameter?
  if(!m.is_static)
  {
    java_method_typet::parameterst &parameters = member_type.parameters();
    java_method_typet::parametert this_p;
    const reference_typet object_ref_type=
      java_reference_type(symbol_typet(class_symbol.name));
    this_p.type()=object_ref_type;
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

  if(java_bytecode_parse_treet::find_annotation(
       m.annotations, "java::org.cprover.MustNotThrow"))
  {
    method_symbol.type.set(ID_C_must_not_throw, true);
  }

  symbol_table.add(method_symbol);
}

void java_bytecode_convert_methodt::convert(
  const symbolt &class_symbol,
  const methodt &m)
{
  // Construct the fully qualified method name
  // (e.g. "my.package.ClassName.myMethodName:(II)I") and query the symbol table
  // to retrieve the symbol (constructed by java_bytecode_convert_method_lazy)
  // associated to the method
  const irep_idt method_identifier=
    id2string(class_symbol.name)+"."+id2string(m.name)+":"+m.descriptor;
  method_id=method_identifier;

  symbolt &method_symbol=*symbol_table.get_writeable(method_identifier);

  // Obtain a std::vector of java_method_typet::parametert objects from the
  // (function) type of the symbol
  java_method_typet method_type = to_java_method_type(method_symbol.type);
  method_type.set(ID_C_class, class_symbol.name);
  method_type.set_is_final(m.is_final);
  method_return_type = method_type.return_type();
  java_method_typet::parameterst &parameters = method_type.parameters();

  // Determine the number of local variable slots used by the JVM to maintain
  // the formal parameters
  slots_for_parameters = java_method_parameter_slots(method_type);

  debug() << "Generating codet: class "
             << class_symbol.name << ", method "
             << m.name << eom;

  // We now set up the local variables for the method parameters
  variables.clear();

  // Find parameter names in the local variable table:
  for(const auto &v : m.local_variable_table)
  {
    // Skip this variable if it is not a method parameter
    if(!is_parameter(v))
      continue;

    // Construct a fully qualified name for the parameter v,
    // e.g. my.package.ClassName.myMethodName:(II)I::anIntParam, and then a
    // symbol_exprt with the parameter and its type
    typet t;
    if(v.signature.has_value())
    {
      t=java_type_from_string_with_exception(
        v.descriptor,
        v.signature,
        id2string(class_symbol.name));
    }
    else
      t=java_type_from_string(v.descriptor);

    std::ostringstream id_oss;
    id_oss << method_id << "::" << v.name;
    irep_idt identifier(id_oss.str());
    symbol_exprt result(identifier, t);
    result.set(ID_C_base_name, v.name);

    // Create a new variablet in the variables vector; in fact this entry will
    // be rewritten below in the loop that iterates through the method
    // parameters; the only field that seem to be useful to write here is the
    // symbol_expr, others will be rewritten
    variables[v.index].push_back(variablet());
    auto &newv=variables[v.index].back();
    newv.symbol_expr=result;
    newv.start_pc=v.start_pc;
    newv.length=v.length;
  }

  // The variables is a expanding_vectort, and the loop above may have expanded
  // the vector introducing gaps where the entries are empty vectors. We now
  // make sure that the vector of each LV slot contains exactly one variablet,
  // possibly default-initialized
  std::size_t param_index=0;
  for(const auto &param : parameters)
  {
    variables[param_index].resize(1);
    param_index+=java_local_variable_slots(param.type());
  }
  INVARIANT(
    param_index==slots_for_parameters,
    "java_parameter_count and local computation must agree");

  // Assign names to parameters
  param_index=0;
  for(auto &param : parameters)
  {
    irep_idt base_name, identifier;

    // Construct a sensible base name (base_name) and a fully qualified name
    // (identifier) for every parameter of the method under translation,
    // regardless of whether we have an LVT or not; and assign it to the
    // parameter object (which is stored in the type of the symbol, not in the
    // symbol table)
    if(param_index==0 && param.get_this())
    {
      // my.package.ClassName.myMethodName:(II)I::this
      base_name="this";
      identifier=id2string(method_identifier)+"::"+id2string(base_name);
    }
    else
    {
      // if already present in the LVT ...
      base_name=variables[param_index][0].symbol_expr.get(ID_C_base_name);
      identifier=variables[param_index][0].symbol_expr.get(ID_identifier);

      // ... then base_name will not be empty
      if(base_name.empty())
      {
        // my.package.ClassName.myMethodName:(II)I::argNT, where N is the local
        // variable slot where the parameter is stored and T is a character
        // indicating the type
        const typet &type=param.type();
        char suffix=java_char_from_type(type);
        base_name="arg"+std::to_string(param_index)+suffix;
        identifier=id2string(method_identifier)+"::"+id2string(base_name);
      }
    }
    param.set_base_name(base_name);
    param.set_identifier(identifier);

    // Build a new symbol for the parameter and add it to the symbol table
    parameter_symbolt parameter_symbol;
    parameter_symbol.base_name=base_name;
    parameter_symbol.mode=ID_java;
    parameter_symbol.name=identifier;
    parameter_symbol.type=param.type();
    symbol_table.add(parameter_symbol);

    // Add as a JVM local variable
    variables[param_index][0].symbol_expr=parameter_symbol.symbol_expr();
    variables[param_index][0].is_parameter=true;
    variables[param_index][0].start_pc=0;
    variables[param_index][0].length=std::numeric_limits<size_t>::max();
    param_index+=java_local_variable_slots(param.type());
  }

  // The parameter slots detected in this function should agree with what
  // java_parameter_count() thinks about this method
  INVARIANT(
    param_index==slots_for_parameters,
    "java_parameter_count and local computation must agree");

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
    method_type.add_throws_exceptions(exception_name);

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
    method_symbol.value = convert_instructions(
      m,
      to_java_class_type(class_symbol.type).lambda_method_handles());
}

const bytecode_infot &java_bytecode_convert_methodt::get_bytecode_info(
  const irep_idt &statement)
{
  for(const bytecode_infot *p=bytecode_info; p->mnemonic!=nullptr; p++)
    if(statement==p->mnemonic)
      return *p;

  error() << "failed to find bytecode mnemonic `"
          << statement << '\'' << eom;
  throw 0;
}

static irep_idt get_if_cmp_operator(const irep_idt &stmt)
{
  if(stmt==patternt("if_?cmplt"))
    return ID_lt;
  if(stmt==patternt("if_?cmple"))
    return ID_le;
  if(stmt==patternt("if_?cmpgt"))
    return ID_gt;
  if(stmt==patternt("if_?cmpge"))
    return ID_ge;
  if(stmt==patternt("if_?cmpeq"))
    return ID_equal;
  if(stmt==patternt("if_?cmpne"))
    return ID_notequal;

  throw "unhandled java comparison instruction";
}

static member_exprt to_member(const exprt &pointer, const exprt &fieldref)
{
  symbol_typet class_type(fieldref.get(ID_class));

  const typecast_exprt pointer2(pointer, java_reference_type(class_type));

  dereference_exprt obj_deref=checked_dereference(pointer2, class_type);

  const member_exprt member_expr(
    obj_deref,
    fieldref.get(ID_component_name),
    fieldref.type());

  return member_expr;
}

/// Find all goto statements in 'repl' that target 'old_label' and redirect them
/// to 'new_label'.
/// \par parameters: 'repl', a block of code in which to perform replacement,
///   and
/// an old_label that should be replaced throughout by new_label.
/// \return None (side-effects on repl)
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
/// \par parameters: 'tree', a code block descriptor, and 'this_block', the
///   corresponding
/// actual code_blockt. 'address_start' and 'address_limit', the Java
/// bytecode offsets searched for. 'next_block_start_address', the
/// bytecode offset of tree/this_block's successor sibling, or UINT_MAX
/// if none exists.
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
/// purpose)
/// \par parameters: See above, plus the bytecode address map 'amap' and
///   'allow_merge'
/// which is always true except when called from get_block_for_pcrange
/// \return See above, plus potential side-effects on 'tree' and 'this_block' as
///   described in 'Purpose'
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
  auto child_iter=this_block.operands().begin();
  // Skip any top-of-block declarations;
  // all other children are labelled subblocks.
  while(child_iter!=this_block.operands().end() &&
        to_code(*child_iter).get_statement()==ID_decl)
    ++child_iter;
  assert(child_iter!=this_block.operands().end());
  std::advance(child_iter, child_offset);
  assert(child_iter!=this_block.operands().end());
  auto &child_label=to_code_label(to_code(*child_iter));
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
        debug() << "Generating codet:  "
                << "warning: refusing to create lexical block spanning "
                << (*findstart) << "-" << findlim_block_start_address
                << " due to incoming edge " << p << " -> "
                << checkit->first << eom;
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
  debug() << "Generating codet:  combining "
          << std::distance(findstart, findlim)
          << " blocks for addresses " << (*findstart) << "-"
          << findlim_block_start_address << eom;

  // Make a new block containing every child of interest:
  auto &this_block_children=this_block.operands();
  assert(tree.branch.size()==this_block_children.size());
  for(auto blockidx=child_offset, blocklim=child_offset+nblocks;
      blockidx!=blocklim;
      ++blockidx)
    newblock.move_to_operands(this_block_children[blockidx]);

  // Relabel the inner header:
  to_code_label(to_code(newblock.operands()[0])).set_label(new_label_irep);
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
        to_code(this_block_children[child_offset])).code());
}

static void gather_symbol_live_ranges(
  java_bytecode_convert_methodt::method_offsett pc,
  const exprt &e,
  std::map<irep_idt, java_bytecode_convert_methodt::variablet> &result)
{
  if(e.id()==ID_symbol)
  {
    const auto &symexpr=to_symbol_expr(e);
    auto findit = result.insert(
      {symexpr.get_identifier(), java_bytecode_convert_methodt::variablet()});
    auto &var=findit.first->second;
    if(findit.second)
    {
      var.symbol_expr=symexpr;
      var.start_pc=pc;
      var.length=1;
    }
    else
    {
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
    code_function_callt ret;
    ret.function() = findit->second.symbol_expr();
    if(needed_lazy_methods)
      needed_lazy_methods->add_needed_method(findit->second.name);
    return ret;
  }
}

static std::size_t get_bytecode_type_width(const typet &ty)
{
  if(ty.id()==ID_pointer)
    return 32;
  return ty.get_size_t(ID_width);
}

codet java_bytecode_convert_methodt::convert_instructions(
  const methodt &method,
  const java_class_typet::java_lambda_method_handlest &lambda_method_handles)
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

    if(i_it->statement!="goto" &&
       i_it->statement!="return" &&
       !(i_it->statement==patternt("?return")) &&
       i_it->statement!="athrow" &&
       i_it->statement!="jsr" &&
       i_it->statement!="jsr_w" &&
       i_it->statement!="ret")
    {
      instructionst::const_iterator next=i_it;
      if(++next!=instructions.end())
        a_entry.first->second.successors.push_back(next->address);
    }

    if(i_it->statement=="athrow" ||
       i_it->statement=="putfield" ||
       i_it->statement=="getfield" ||
       i_it->statement=="checkcast" ||
       i_it->statement=="newarray" ||
       i_it->statement=="anewarray" ||
       i_it->statement=="idiv" ||
       i_it->statement=="ldiv" ||
       i_it->statement=="irem" ||
       i_it->statement=="lrem" ||
       i_it->statement==patternt("?astore") ||
       i_it->statement==patternt("?aload") ||
       i_it->statement=="invokestatic" ||
       i_it->statement=="invokevirtual" ||
       i_it->statement=="invokespecial" ||
       i_it->statement=="invokeinterface" ||
       (threading_support && (i_it->statement=="monitorenter" ||
       i_it->statement=="monitorexit")))
    {
      const std::vector<method_offsett> handler =
        try_catch_handler(i_it->address, method.exception_table);
      std::list<method_offsett> &successors = a_entry.first->second.successors;
      successors.insert(successors.end(), handler.begin(), handler.end());
      targets.insert(handler.begin(), handler.end());
    }

    if(i_it->statement=="goto" ||
       i_it->statement==patternt("if_?cmp??") ||
       i_it->statement==patternt("if??") ||
       i_it->statement=="ifnonnull" ||
       i_it->statement=="ifnull" ||
       i_it->statement=="jsr" ||
       i_it->statement=="jsr_w")
    {
      PRECONDITION(!i_it->args.empty());

      unsigned target;
      bool ret=to_unsigned_integer(to_constant_expr(i_it->args[0]), target);
      DATA_INVARIANT(!ret, "target expected to be unsigned integer");
      targets.insert(target);

      a_entry.first->second.successors.push_back(target);

      if(i_it->statement=="jsr" ||
         i_it->statement=="jsr_w")
      {
        auto next = std::next(i_it);
        DATA_INVARIANT(
          next != instructions.end(), "jsr should have valid return address");
        targets.insert(next->address);
        jsr_ret_targets.push_back(next->address);
      }
    }
    else if(i_it->statement=="tableswitch" ||
            i_it->statement=="lookupswitch")
    {
      bool is_label=true;
      for(const auto &arg : i_it->args)
      {
        if(is_label)
        {
          unsigned target;
          bool ret=to_unsigned_integer(to_constant_expr(arg), target);
          DATA_INVARIANT(!ret, "target expected to be unsigned integer");
          targets.insert(target);
          a_entry.first->second.successors.push_back(target);
        }
        is_label=!is_label;
      }
    }
    else if(i_it->statement=="ret")
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

    irep_idt statement=i_it->statement;
    exprt arg0=i_it->args.size()>=1?i_it->args[0]:nil_exprt();
    exprt arg1=i_it->args.size()>=2?i_it->args[1]:nil_exprt();

    const bytecode_infot &bytecode_info=get_bytecode_info(statement);

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
      statement=std::string(id2string(statement), 0, statement.size()-2);
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
        if(catch_type != typet() || it->catch_type == symbol_typet(irep_idt()))
        {
          catch_type=symbol_typet("java::java.lang.Throwable");
          break;
        }
        else
          catch_type=it->catch_type;
      }
    }

    codet catch_instruction;

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
      code_landingpadt catch_statement(catch_var);
      catch_instruction=catch_statement;
    }

    exprt::operandst op=pop(bytecode_info.pop);
    exprt::operandst results;
    results.resize(bytecode_info.push, nil_exprt());

    if(statement=="aconst_null")
    {
      assert(results.size()==1);
      results[0]=null_pointer_exprt(java_reference_type(void_typet()));
    }
    else if(statement=="athrow")
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);
      convert_athrow(i_it->source_location, op, c, results);
    }
    else if(statement=="checkcast")
    {
      // checkcast throws an exception in case a cast of object
      // on stack to given type fails.
      // The stack isn't modified.
      PRECONDITION(op.size() == 1 && results.size() == 1);
      convert_checkcast(arg0, op, c, results);
    }
    else if(statement=="invokedynamic")
    {
      // not used in Java
      if(
        const auto res = convert_invoke_dynamic(
          lambda_method_handles, i_it->source_location, arg0))
      {
        results.resize(1);
        results[0] = *res;
      }
    }
    else if(statement=="invokestatic" &&
            id2string(arg0.get(ID_identifier))==
            "java::org.cprover.CProver.assume:(Z)V")
    {
      const java_method_typet &method_type = to_java_method_type(arg0.type());
      INVARIANT(
        method_type.parameters().size() == 1,
        "function expected to have exactly one parameter");
      c = replace_call_to_cprover_assume(i_it->source_location, c);
    }
    // replace calls to CProver.atomicBegin
    else if(statement == "invokestatic" &&
            arg0.get(ID_identifier) ==
            "java::org.cprover.CProver.atomicBegin:()V")
    {
      c = codet(ID_atomic_begin);
    }
    // replace calls to CProver.atomicEnd
    else if(statement == "invokestatic" &&
            arg0.get(ID_identifier) ==
            "java::org.cprover.CProver.atomicEnd:()V")
    {
      c = codet(ID_atomic_end);
    }
    else if(statement=="invokeinterface" ||
            statement=="invokespecial" ||
            statement=="invokevirtual" ||
            statement=="invokestatic")
    {
      convert_invoke(i_it->source_location, statement, arg0, c, results);
    }
    else if(statement=="return")
    {
      PRECONDITION(op.empty() && results.empty());
      c=code_returnt();
    }
    else if(statement==patternt("?return"))
    {
      // Return types are promoted in java, so this might need
      // conversion.
      PRECONDITION(op.size() == 1 && results.empty());
      exprt r=op[0];
      if(r.type()!=method_return_type)
        r=typecast_exprt(r, method_return_type);
      c=code_returnt(r);
    }
    else if(statement==patternt("?astore"))
    {
      assert(op.size()==3 && results.empty());
      c = convert_astore(statement, op, i_it->source_location);
    }
    else if(statement==patternt("?store"))
    {
      // store value into some local variable
      PRECONDITION(op.size() == 1 && results.empty());
      c = convert_store(
        statement, arg0, op, i_it->address, i_it->source_location);
    }
    else if(statement==patternt("?aload"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0] = convert_aload(statement, op);
    }
    else if(statement==patternt("?load"))
    {
      // load a value from a local variable
      results[0]=
        variable(arg0, statement[0], i_it->address, CAST_AS_NEEDED);
    }
    else if(statement=="ldc" || statement=="ldc_w" ||
            statement=="ldc2" || statement=="ldc2_w")
    {
      PRECONDITION(op.empty() && results.size() == 1);

      INVARIANT(
        arg0.id() != ID_java_string_literal && arg0.id() != ID_type,
        "String and Class literals should have been lowered in "
        "generate_constant_global_variables");

      results[0] = arg0;
    }
    else if(statement=="goto" || statement=="goto_w")
    {
      PRECONDITION(op.empty() && results.empty());
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg0), number);
      INVARIANT(!ret, "goto argument should be an integer");
      code_gotot code_goto(label(integer2string(number)));
      c=code_goto;
    }
    else if(statement=="jsr" || statement=="jsr_w")
    {
      // As 'goto', except we must also push the subroutine return address:
      PRECONDITION(op.empty() && results.size() == 1);
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg0), number);
      INVARIANT(!ret, "jsr argument should be an integer");
      code_gotot code_goto(label(integer2string(number)));
      c=code_goto;
      results[0]=
        from_integer(
          std::next(i_it)->address,
          unsignedbv_typet(64));
      results[0].type()=pointer_type(void_typet());
    }
    else if(statement=="ret")
    {
      // Since we have a bounded target set, make life easier on our analyses
      // and write something like:
      // if(retaddr==5) goto 5; else if(retaddr==10) goto 10; ...
      PRECONDITION(op.empty() && results.empty());
      assert(!jsr_ret_targets.empty());
      c = convert_ret(
        jsr_ret_targets, arg0, i_it->source_location, i_it->address);
    }
    else if(statement=="iconst_m1")
    {
      assert(results.size()==1);
      results[0]=from_integer(-1, java_int_type());
    }
    else if(statement==patternt("?const"))
    {
      assert(results.size()==1);
      results = convert_const(statement, arg0, results);
    }
    else if(statement==patternt("?ipush"))
    {
      PRECONDITION(results.size()==1);
      DATA_INVARIANT(
        arg0.id()==ID_constant,
        "ipush argument expected to be constant");
      results[0]=arg0;
      if(arg0.type()!=java_int_type())
        results[0].make_typecast(java_int_type());
    }
    else if(statement==patternt("if_?cmp??"))
    {
      PRECONDITION(op.size() == 2 && results.empty());
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg0), number);
      INVARIANT(!ret, "if_?cmp?? argument should be an integer");
      c = convert_if_cmp(
        address_map, statement, op, number, i_it->source_location);
    }
    else if(statement==patternt("if??"))
    {
      const irep_idt id=
        statement=="ifeq"?ID_equal:
        statement=="ifne"?ID_notequal:
        statement=="iflt"?ID_lt:
        statement=="ifge"?ID_ge:
        statement=="ifgt"?ID_gt:
        statement=="ifle"?ID_le:
        irep_idt();

      INVARIANT(!id.empty(), "unexpected bytecode-if");
      PRECONDITION(op.size() == 1 && results.empty());
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg0), number);
      INVARIANT(!ret, "if?? argument should be an integer");
      c = convert_if(address_map, op, id, number, i_it->source_location);
    }
    else if(statement==patternt("ifnonnull"))
    {
      PRECONDITION(op.size() == 1 && results.empty());
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg0), number);
      INVARIANT(!ret, "ifnonnull argument should be an integer");
      c = convert_ifnonull(address_map, op, number, i_it->source_location);
    }
    else if(statement==patternt("ifnull"))
    {
      PRECONDITION(op.size() == 1 && results.empty());
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg0), number);
      INVARIANT(!ret, "ifnull argument should be an integer");
      c = convert_ifnull(address_map, op, number, i_it->source_location);
    }
    else if(statement=="iinc")
    {
      c = convert_iinc(arg0, arg1, i_it->source_location, i_it->address);
    }
    else if(statement==patternt("?xor"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=bitxor_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?or"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=bitor_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?and"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=bitand_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?shl"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=shl_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?shr"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=ashr_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?ushr"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results = convert_ushr(statement, op, results);
    }
    else if(statement==patternt("?add"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=plus_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?sub"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=minus_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?div"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=div_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?mul"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=mult_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?neg"))
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);
      results[0]=unary_minus_exprt(op[0], op[0].type());
    }
    else if(statement==patternt("?rem"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      if(statement=="frem" || statement=="drem")
        results[0]=rem_exprt(op[0], op[1]);
      else
        results[0]=mod_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?cmp"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results = convert_cmp(op, results);
    }
    else if(statement==patternt("?cmp?"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results = convert_cmp2(statement, op, results);
    }
    else if(statement==patternt("?cmpl"))
    {
      PRECONDITION(op.size() == 2 && results.size() == 1);
      results[0]=binary_relation_exprt(op[0], ID_lt, op[1]);
    }
    else if(statement=="dup")
    {
      PRECONDITION(op.size() == 1 && results.size() == 2);
      results[0]=results[1]=op[0];
    }
    else if(statement=="dup_x1")
    {
      PRECONDITION(op.size() == 2 && results.size() == 3);
      results[0]=op[1];
      results[1]=op[0];
      results[2]=op[1];
    }
    else if(statement=="dup_x2")
    {
      PRECONDITION(op.size() == 3 && results.size() == 4);
      results[0]=op[2];
      results[1]=op[0];
      results[2]=op[1];
      results[3]=op[2];
    }
    // dup2* behaviour depends on the size of the operands on the
    // stack
    else if(statement=="dup2")
    {
      PRECONDITION(!stack.empty() && results.empty());
      convert_dup2(op, results);
    }
    else if(statement=="dup2_x1")
    {
      PRECONDITION(!stack.empty() && results.empty());
      convert_dup2_x1(op, results);
    }
    else if(statement=="dup2_x2")
    {
      PRECONDITION(!stack.empty() && results.empty());
      convert_dup2_x2(op, results);
    }
    else if(statement=="dconst")
    {
      PRECONDITION(op.empty() && results.size() == 1);
    }
    else if(statement=="fconst")
    {
      PRECONDITION(op.empty() && results.size() == 1);
    }
    else if(statement=="getfield")
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);
      results[0]=java_bytecode_promotion(to_member(op[0], arg0));
    }
    else if(statement=="getstatic")
    {
      PRECONDITION(op.empty() && results.size() == 1);
      symbol_exprt symbol_expr(arg0.type());
      const auto &field_name=arg0.get_string(ID_component_name);
      const bool is_assertions_disabled_field=
        field_name.find("$assertionsDisabled")!=std::string::npos;

      symbol_expr.set_identifier(
        get_static_field(arg0.get_string(ID_class), field_name));

      INVARIANT(
        symbol_table.has_symbol(symbol_expr.get_identifier()),
        "getstatic symbol should have been created before method conversion");

      convert_getstatic(
        arg0, symbol_expr, is_assertions_disabled_field, c, results);
    }
    else if(statement=="putfield")
    {
      PRECONDITION(op.size() == 2 && results.empty());
      c = convert_putfield(arg0, op);
    }
    else if(statement=="putstatic")
    {
      PRECONDITION(op.size() == 1 && results.empty());
      symbol_exprt symbol_expr(arg0.type());
      const auto &field_name=arg0.get_string(ID_component_name);
      symbol_expr.set_identifier(
        get_static_field(arg0.get_string(ID_class), field_name));

      INVARIANT(
        symbol_table.has_symbol(symbol_expr.get_identifier()),
        "putstatic symbol should have been created before method conversion");

      c = convert_putstatic(i_it->source_location, arg0, op, symbol_expr);
    }
    else if(statement==patternt("?2?")) // i2c etc.
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);
      typet type=java_type_from_char(statement[2]);
      results[0]=op[0];
      if(results[0].type()!=type)
        results[0].make_typecast(type);
    }
    else if(statement=="new")
    {
      // use temporary since the stack symbol might get duplicated
      PRECONDITION(op.empty() && results.size() == 1);
      convert_new(i_it->source_location, arg0, c, results);
    }
    else if(statement=="newarray" ||
            statement=="anewarray")
    {
      // the op is the array size
      PRECONDITION(op.size() == 1 && results.size() == 1);
      convert_newarray(i_it->source_location, statement, arg0, op, c, results);
    }
    else if(statement=="multianewarray")
    {
      // The first argument is the type, the second argument is the number of
      // dimensions.  The size of each dimension is on the stack.
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg1), number);
      INVARIANT(!ret, "multianewarray argument should be an integer");
      std::size_t dimension=integer2size_t(number);

      op=pop(dimension);
      assert(results.size()==1);
      convert_multianewarray(i_it->source_location, arg0, op, c, results);
    }
    else if(statement=="arraylength")
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);

      const typecast_exprt pointer(op[0], java_array_type(statement[0]));

      dereference_exprt array(pointer, pointer.type().subtype());
      PRECONDITION(pointer.type().subtype().id() == ID_symbol_type);
      array.set(ID_java_member_access, true);

      const member_exprt length(array, "length", java_int_type());

      results[0]=length;
    }
    else if(statement=="tableswitch" ||
            statement=="lookupswitch")
    {
      PRECONDITION(op.size() == 1 && results.empty());
      c = convert_switch(address_map, op, i_it->args, i_it->source_location);
    }
    else if(statement=="pop" || statement=="pop2")
    {
      c = convert_pop(statement, op);
    }
    else if(statement=="instanceof")
    {
      PRECONDITION(op.size() == 1 && results.size() == 1);

      results[0]=
        binary_predicate_exprt(op[0], ID_java_instanceof, arg0);
    }
    else if(statement == "monitorenter" || statement == "monitorexit")
    {
      c = convert_monitorenterexit(statement, op, i_it->source_location);
    }
    else if(statement=="swap")
    {
      PRECONDITION(op.size() == 2 && results.size() == 2);
      results[1]=op[0];
      results[0]=op[1];
    }
    else if(statement=="nop")
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
    if(catch_instruction!=codet())
    {
      c.make_block();
      c.operands().insert(c.operands().begin(), catch_instruction);
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
            more_code.copy_to_operands(a);

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
            more_code.copy_to_operands(a);

            expr.swap(lhs);
            ++os_it;
          }
        }

        if(results.empty())
        {
          more_code.copy_to_operands(c);
          c.swap(more_code);
        }
        else
        {
          c.make_block();
          auto &last_statement=to_code_block(c).find_last_statement();
          if(last_statement.get_statement()==ID_goto)
          {
            // Insert stack twiddling before branch:
            last_statement.make_block();
            last_statement.operands().insert(
              last_statement.operands().begin(),
              more_code.operands().begin(),
              more_code.operands().end());
          }
          else
            forall_operands(o_it, more_code)
              c.copy_to_operands(*o_it);
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
    // Start a new lexical block if we've just entered a try block
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
      code_labelt newlabel(label(std::to_string(address)), code_blockt());
      root_block.move_to_operands(newlabel);
      root.branch.push_back(block_tree_nodet::get_leaf());
      assert((root.branch_addresses.empty() ||
              root.branch_addresses.back()<address) &&
             "Block addresses should be unique and increasing");
      root.branch_addresses.push_back(address);
    }

    if(c.get_statement()!=ID_skip)
    {
      auto &lastlabel=to_code_label(to_code(root_block.operands().back()));
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
    block.operands().insert(block.operands().begin(), d);
  }

  for(auto &block : root_block.operands())
    code.move_to_operands(block);

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

codet java_bytecode_convert_methodt::convert_switch(
  java_bytecode_convert_methodt::address_mapt &address_map,
  const exprt::operandst &op,
  const java_bytecode_parse_treet::instructiont::argst &args,
  const source_locationt &location)
{
  // we turn into switch-case
  code_switcht code_switch;
  code_switch.add_source_location() = location;
  code_switch.value() = op[0];
  code_blockt code_block;
  code_block.add_source_location() = location;

  bool is_label = true;
  for(auto a_it = args.begin(); a_it != args.end();
      a_it++, is_label = !is_label)
  {
    if(is_label)
    {
      code_switch_caset code_case;
      code_case.add_source_location() = location;

      mp_integer number;
      bool ret = to_integer(to_constant_expr(*a_it), number);
      DATA_INVARIANT(!ret, "case label expected to be integer");
      // The switch case does not contain any code, it just branches via a GOTO
      // to the jump target of the tableswitch/lookupswitch case at
      // hand. Therefore we consider this code to belong to the source bytecode
      // instruction and not the target instruction.
      const method_offsett label_number =
        numeric_cast_v<method_offsett>(number);
      code_case.code() = code_gotot(label(std::to_string(label_number)));
      code_case.code().add_source_location() = location;

      if(a_it == args.begin())
        code_case.set_default();
      else
      {
        auto prev = a_it;
        prev--;
        code_case.case_op() = *prev;
        if(code_case.case_op().type() != op[0].type())
          code_case.case_op().make_typecast(op[0].type());
        code_case.case_op().add_source_location() = location;
      }

      code_block.add(code_case);
    }
  }

  code_switch.body() = code_block;
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
    {java_method_typet::parametert(java_reference_type(void_typet()))},
    void_typet());
  code_function_callt call;
  call.function() = symbol_exprt(descriptor, type);
  call.lhs().make_nil();
  call.arguments().push_back(op[0]);
  call.add_source_location() = source_location;
  if(needed_lazy_methods && symbol_table.has_symbol(descriptor))
    needed_lazy_methods->add_needed_method(descriptor);
  return call;
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
  const exprt &arg0,
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
      mp_integer number;
      bool ret = to_integer(to_constant_expr(arg0), number);
      DATA_INVARIANT(!ret, "failed to convert constant");
      value.from_integer(number);
    }
    else
      value.from_expr(to_constant_expr(arg0));

    results[0] = value.to_expr();
  }
  else
  {
    mp_integer value;
    bool ret = to_integer(to_constant_expr(arg0), value);
    DATA_INVARIANT(!ret, "failed to convert constant");
    const typet type = java_type_from_char(statement[0]);
    results[0] = from_integer(value, type);
  }
  return results;
}

void java_bytecode_convert_methodt::convert_invoke(
  source_locationt location,
  const irep_idt &statement,
  exprt &arg0,
  codet &c,
  exprt::operandst &results)
{
  const bool use_this(statement != "invokestatic");
  const bool is_virtual(
    statement == "invokevirtual" || statement == "invokeinterface");

  java_method_typet &method_type = to_java_method_type(arg0.type());
  java_method_typet::parameterst &parameters(method_type.parameters());

  if(use_this)
  {
    if(parameters.empty() || !parameters[0].get_this())
    {
      irep_idt classname = arg0.get(ID_C_class);
      typet thistype = symbol_typet(classname);
      // Note invokespecial is used for super-method calls as well as
      // constructors.
      if(statement == "invokespecial")
      {
        if(is_constructor(arg0.get(ID_identifier)))
        {
          if(needed_lazy_methods)
            needed_lazy_methods->add_needed_class(classname);
          method_type.set_is_constructor();
        }
        else
          method_type.set(ID_java_super_method_call, true);
      }
      reference_typet object_ref_type = java_reference_type(thistype);
      java_method_typet::parametert this_p(object_ref_type);
      this_p.set_this();
      this_p.set_base_name("this");
      parameters.insert(parameters.begin(), this_p);
    }
  }

  code_function_callt call;
  location.set_function(method_id);

  call.add_source_location() = location;
  call.arguments() = pop(parameters.size());

  // double-check a bit
  if(use_this)
  {
    const exprt &this_arg = call.arguments().front();
    INVARIANT(
      this_arg.type().id() == ID_pointer, "first argument must be a pointer");
  }

  // do some type adjustment for the arguments,
  // as Java promotes arguments
  // Also cast pointers since intermediate locals
  // can be void*.

  for(std::size_t i = 0; i < parameters.size(); i++)
  {
    const typet &type = parameters[i].type();
    if(
      type == java_boolean_type() || type == java_char_type() ||
      type == java_byte_type() || type == java_short_type() ||
      type.id() == ID_pointer)
    {
      assert(i < call.arguments().size());
      if(type != call.arguments()[i].type())
        call.arguments()[i].make_typecast(type);
    }
  }

  // do some type adjustment for return values

  const typet &return_type = method_type.return_type();

  if(return_type.id() != ID_empty)
  {
    // return types are promoted in Java
    call.lhs() = tmp_variable("return", return_type);
    exprt promoted = java_bytecode_promotion(call.lhs());
    results.resize(1);
    results[0] = promoted;
  }

  assert(arg0.id() == ID_virtual_function);

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
  irep_idt id = arg0.get(ID_identifier);
  if(
    symbol_table.symbols.find(id) == symbol_table.symbols.end() &&
    !(is_virtual &&
      is_method_inherited(arg0.get(ID_C_class), arg0.get(ID_component_name))))
  {
    symbolt symbol;
    symbol.name = id;
    symbol.base_name = arg0.get(ID_C_base_name);
    symbol.pretty_name = id2string(arg0.get(ID_C_class)).substr(6) + "." +
                         id2string(symbol.base_name) + "()";
    symbol.type = arg0.type();
    symbol.type.set(ID_access, ID_private);
    to_java_method_type(symbol.type).set_is_final(true);
    symbol.value.make_nil();
    symbol.mode = ID_java;
    assign_parameter_names(
      to_java_method_type(symbol.type), symbol.name, symbol_table);

    debug() << "Generating codet:  new opaque symbol: method '" << symbol.name
            << "'" << eom;
    symbol_table.add(symbol);
  }

  if(is_virtual)
  {
    // dynamic binding
    assert(use_this);
    assert(!call.arguments().empty());
    call.function() = arg0;
    // Populate needed methods later,
    // once we know what object types can exist.
  }
  else
  {
    // static binding
    call.function() = symbol_exprt(arg0.get(ID_identifier), arg0.type());
    if(needed_lazy_methods)
    {
      needed_lazy_methods->add_needed_method(arg0.get(ID_identifier));
      // Calling a static method causes static initialization:
      needed_lazy_methods->add_needed_class(arg0.get(ID_C_class));
    }
  }

  call.function().add_source_location() = location;

  // Replacing call if it is a function of the Character library,
  // returning the same call otherwise
  c = string_preprocess.replace_character_call(call);

  if(!use_this)
  {
    codet clinit_call = get_clinit_call(arg0.get(ID_C_class));
    if(clinit_call.get_statement() != ID_skip)
    {
      code_blockt ret_block;
      ret_block.move_to_operands(clinit_call);
      ret_block.move_to_operands(c);
      c = std::move(ret_block);
    }
  }
}

codet &java_bytecode_convert_methodt::replace_call_to_cprover_assume(
  source_locationt location,
  codet &c)
{
  exprt operand = pop(1)[0];
  // we may need to adjust the type of the argument
  if(operand.type() != bool_typet())
    operand.make_typecast(bool_typet());

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
  binary_predicate_exprt check(op[0], ID_java_instanceof, arg0);
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
    !throw_assertion_error &&
    uncaught_exceptions_domaint::get_exception_type(op[0].type()) ==
      "java::java.lang.AssertionError")
  {
    // we translate athrow into
    // ASSERT false;
    // ASSUME false:
    code_assertt assert_code;
    assert_code.assertion() = false_exprt();
    source_locationt assert_location = location; // copy
    assert_location.set_comment("assertion at " + location.as_string());
    assert_location.set("user-provided", true);
    assert_location.set_property_class(ID_assertion);
    assert_code.add_source_location() = assert_location;

    code_assumet assume_code;
    assume_code.assumption() = false_exprt();
    source_locationt assume_location = location; // copy
    assume_location.set("user-provided", true);
    assume_code.add_source_location() = assume_location;

    code_blockt ret_block;
    ret_block.move_to_operands(assert_code);
    ret_block.move_to_operands(assume_code);
    c = ret_block;
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
  codet &c)
{
  std::vector<irep_idt> exception_ids;
  std::vector<irep_idt> handler_labels;

  // for each try-catch add a CATCH-PUSH instruction
  // each CATCH-PUSH records a list of all the handler labels
  // together with a list of all the exception ids

  // be aware of different try-catch blocks with the same starting pc
  method_offsett pos = 0;
  method_offsett end_pc = 0;
  while(pos < method.exception_table.size())
  {
    // check if this is the beginning of a try block
    for(; pos < method.exception_table.size(); ++pos)
    {
      // unexplored try-catch?
      if(cur_pc == method.exception_table[pos].start_pc && end_pc == 0)
      {
        end_pc = method.exception_table[pos].end_pc;
      }

      // currently explored try-catch?
      if(
        cur_pc == method.exception_table[pos].start_pc &&
        method.exception_table[pos].end_pc == end_pc)
      {
        exception_ids.push_back(
          method.exception_table[pos].catch_type.get_identifier());
        // record the exception handler in the CATCH-PUSH
        // instruction by generating a label corresponding to
        // the handler's pc
        handler_labels.push_back(
          label(std::to_string(method.exception_table[pos].handler_pc)));
      }
      else
        break;
    }

    // add the actual PUSH-CATCH instruction
    if(!exception_ids.empty())
    {
      code_push_catcht catch_push;
      INVARIANT(
        exception_ids.size() == handler_labels.size(),
        "Exception tags and handler labels should be 1-to-1");
      code_push_catcht::exception_listt &exception_list =
        catch_push.exception_list();
      for(size_t i = 0; i < exception_ids.size(); ++i)
      {
        exception_list.push_back(
          code_push_catcht::exception_list_entryt(
            exception_ids[i], handler_labels[i]));
      }

      code_blockt try_block;
      try_block.move_to_operands(catch_push);
      try_block.move_to_operands(c);
      c = try_block;
    }
    else
    {
      // advance
      ++pos;
    }

    // reset
    end_pc = 0;
    exception_ids.clear();
    handler_labels.clear();
  }

  // next add the CATCH-POP instructions
  size_t start_pc = 0;
  // as the first try block may have start_pc 0, we
  // must track it separately
  bool first_handler = false;
  // check if this is the end of a try block
  for(const auto &exception_row : method.exception_table)
  {
    // add the CATCH-POP before the end of the try block
    if(
      cur_pc < exception_row.end_pc && !working_set.empty() &&
      *working_set.begin() == exception_row.end_pc)
    {
      // have we already added a CATCH-POP for the current try-catch?
      // (each row corresponds to a handler)
      if(exception_row.start_pc != start_pc || !first_handler)
      {
        if(!first_handler)
          first_handler = true;
        // remember the beginning of the try-catch so that we don't add
        // another CATCH-POP for the same try-catch
        start_pc = exception_row.start_pc;
        // add CATCH_POP instruction
        code_pop_catcht catch_pop;
        code_blockt end_try_block;
        end_try_block.move_to_operands(c);
        end_try_block.move_to_operands(catch_pop);
        c = end_try_block;
      }
    }
  }
  return c;
}

void java_bytecode_convert_methodt::convert_multianewarray(
  const source_locationt &location,
  const exprt &arg0,
  const exprt::operandst &op,
  codet &c,
  exprt::operandst &results)
{
  PRECONDITION(!location.get_line().empty());
  const reference_typet ref_type = java_reference_type(arg0.type());
  side_effect_exprt java_new_array(ID_java_new_array, ref_type, location);
  java_new_array.operands() = op;

  code_blockt create;

  if(max_array_length != 0)
  {
    constant_exprt size_limit = from_integer(max_array_length, java_int_type());
    binary_relation_exprt le_max_size(op[0], ID_le, size_limit);
    code_assumet assume_le_max_size(le_max_size);
    create.move_to_operands(assume_le_max_size);
  }

  const exprt tmp = tmp_variable("newarray", ref_type);
  create.copy_to_operands(code_assignt(tmp, java_new_array));
  c = std::move(create);
  results[0] = tmp;
}

void java_bytecode_convert_methodt::convert_newarray(
  const source_locationt &location,
  const irep_idt &statement,
  const exprt &arg0,
  const exprt::operandst &op,
  codet &c,
  exprt::operandst &results)
{
  char element_type;

  if(statement == "newarray")
  {
    irep_idt id = arg0.type().id();

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
  }
  else
    element_type = 'a';

  const reference_typet ref_type = java_array_type(element_type);

  side_effect_exprt java_new_array(ID_java_new_array, ref_type, location);
  java_new_array.copy_to_operands(op[0]);

  c = code_blockt();

  if(max_array_length != 0)
  {
    constant_exprt size_limit = from_integer(max_array_length, java_int_type());
    binary_relation_exprt le_max_size(op[0], ID_le, size_limit);
    code_assumet assume_le_max_size(le_max_size);
    c.move_to_operands(assume_le_max_size);
  }
  const exprt tmp = tmp_variable("newarray", ref_type);
  c.copy_to_operands(code_assignt(tmp, java_new_array));
  results[0] = tmp;
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
    get_clinit_call(to_symbol_type(arg0.type()).get_identifier());
  if(clinit_call.get_statement() != ID_skip)
  {
    code_blockt ret_block;
    ret_block.move_to_operands(clinit_call);
    ret_block.move_to_operands(c);
    c = std::move(ret_block);
  }
  results[0] = tmp;
}

codet java_bytecode_convert_methodt::convert_putstatic(
  const source_locationt &location,
  const exprt &arg0,
  const exprt::operandst &op,
  const symbol_exprt &symbol_expr)
{
  if(needed_lazy_methods && arg0.type().id() == ID_symbol_type)
  {
    needed_lazy_methods->add_needed_class(
      to_symbol_type(arg0.type()).get_identifier());
  }

  code_blockt block;
  block.add_source_location() = location;

  // Note this initializer call deliberately inits the class used to make
  // the reference, which may be a child of the class that actually defines
  // the field.
  codet clinit_call = get_clinit_call(arg0.get_string(ID_class));
  if(clinit_call.get_statement() != ID_skip)
    block.move_to_operands(clinit_call);

  save_stack_entries(
    "stack_static_field",
    symbol_expr.type(),
    block,
    bytecode_write_typet::STATIC_FIELD,
    symbol_expr.get_identifier());
  block.copy_to_operands(code_assignt(symbol_expr, op[0]));
  return block;
}

codet java_bytecode_convert_methodt::convert_putfield(
  const exprt &arg0,
  const exprt::operandst &op)
{
  code_blockt block;
  save_stack_entries(
    "stack_field",
    op[1].type(),
    block,
    bytecode_write_typet::FIELD,
    arg0.get(ID_component_name));
  block.copy_to_operands(code_assignt(to_member(op[0], arg0), op[1]));
  return block;
}

void java_bytecode_convert_methodt::convert_getstatic(
  const exprt &arg0,
  const symbol_exprt &symbol_expr,
  const bool is_assertions_disabled_field,
  codet &c,
  exprt::operandst &results)
{
  if(needed_lazy_methods)
  {
    if(arg0.type().id() == ID_symbol_type)
    {
      needed_lazy_methods->add_needed_class(
        to_symbol_type(arg0.type()).get_identifier());
    }
    else if(arg0.type().id() == ID_pointer)
    {
      const auto &pointer_type = to_pointer_type(arg0.type());
      if(pointer_type.subtype().id() == ID_symbol_type)
      {
        needed_lazy_methods->add_needed_class(
          to_symbol_type(pointer_type.subtype()).get_identifier());
      }
    }
    else if(is_assertions_disabled_field)
    {
      needed_lazy_methods->add_needed_class(arg0.get_string(ID_class));
    }
  }
  results[0] = java_bytecode_promotion(symbol_expr);

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

exprt::operandst &java_bytecode_convert_methodt::convert_ushr(
  const irep_idt &statement,
  const exprt::operandst &op,
  exprt::operandst &results) const
{
  const typet type = java_type_from_char(statement[0]);

  const std::size_t width = type.get_size_t(ID_width);
  typet target = unsignedbv_typet(width);

  exprt lhs = op[0];
  if(lhs.type() != target)
    lhs.make_typecast(target);
  exprt rhs = op[1];
  if(rhs.type() != target)
    rhs.make_typecast(target);

  results[0] = lshr_exprt(lhs, rhs);
  if(results[0].type() != op[0].type())
    results[0].make_typecast(op[0].type());
  return results;
}

codet java_bytecode_convert_methodt::convert_iinc(
  const exprt &arg0,
  const exprt &arg1,
  const source_locationt &location,
  const method_offsett address)
{
  code_blockt block;
  block.add_source_location() = location;
  // search variable on stack
  const exprt &locvar = variable(arg0, 'i', address, NO_CAST);
  save_stack_entries(
    "stack_iinc",
    java_int_type(),
    block,
    bytecode_write_typet::VARIABLE,
    to_symbol_expr(locvar).get_identifier());

  code_assignt code_assign;
  code_assign.lhs() = variable(arg0, 'i', address, NO_CAST);
  exprt arg1_int_type = arg1;
  if(arg1.type() != java_int_type())
    arg1_int_type.make_typecast(java_int_type());
  code_assign.rhs() =
    plus_exprt(variable(arg0, 'i', address, CAST_AS_NEEDED), arg1_int_type);
  block.copy_to_operands(code_assign);
  return block;
}

codet java_bytecode_convert_methodt::convert_ifnull(
  const java_bytecode_convert_methodt::address_mapt &address_map,
  const exprt::operandst &op,
  const mp_integer &number,
  const source_locationt &location) const
{
  code_ifthenelset code_branch;
  const typecast_exprt lhs(op[0], java_reference_type(empty_typet()));
  const exprt rhs(null_pointer_exprt(to_pointer_type(lhs.type())));
  code_branch.cond() = binary_relation_exprt(lhs, ID_equal, rhs);
  const method_offsett label_number = numeric_cast_v<method_offsett>(number);
  code_branch.then_case() = code_gotot(label(std::to_string(label_number)));
  code_branch.then_case().add_source_location() =
    address_map.at(label_number).source->source_location;
  code_branch.add_source_location() = location;
  return code_branch;
}

codet java_bytecode_convert_methodt::convert_ifnonull(
  const java_bytecode_convert_methodt::address_mapt &address_map,
  const exprt::operandst &op,
  const mp_integer &number,
  const source_locationt &location) const
{
  code_ifthenelset code_branch;
  const typecast_exprt lhs(op[0], java_reference_type(empty_typet()));
  const exprt rhs(null_pointer_exprt(to_pointer_type(lhs.type())));
  code_branch.cond() = binary_relation_exprt(lhs, ID_notequal, rhs);
  const method_offsett label_number = numeric_cast_v<method_offsett>(number);
  code_branch.then_case() = code_gotot(label(std::to_string(label_number)));
  code_branch.then_case().add_source_location() =
    address_map.at(label_number).source->source_location;
  code_branch.add_source_location() = location;
  return code_branch;
}

codet java_bytecode_convert_methodt::convert_if(
  const java_bytecode_convert_methodt::address_mapt &address_map,
  const exprt::operandst &op,
  const irep_idt &id,
  const mp_integer &number,
  const source_locationt &location) const
{
  code_ifthenelset code_branch;
  code_branch.cond() =
    binary_relation_exprt(op[0], id, from_integer(0, op[0].type()));
  code_branch.cond().add_source_location() = location;
  code_branch.cond().add_source_location().set_function(method_id);
  const method_offsett label_number = numeric_cast_v<method_offsett>(number);
  code_branch.then_case() = code_gotot(label(std::to_string(label_number)));
  code_branch.then_case().add_source_location() =
    address_map.at(label_number).source->source_location;
  code_branch.then_case().add_source_location().set_function(method_id);
  code_branch.add_source_location() = location;
  code_branch.add_source_location().set_function(method_id);
  return code_branch;
}

codet java_bytecode_convert_methodt::convert_if_cmp(
  const java_bytecode_convert_methodt::address_mapt &address_map,
  const irep_idt &statement,
  const exprt::operandst &op,
  const mp_integer &number,
  const source_locationt &location) const
{
  code_ifthenelset code_branch;
  const irep_idt cmp_op = get_if_cmp_operator(statement);

  binary_relation_exprt condition(op[0], cmp_op, op[1]);

  exprt &lhs(condition.lhs());
  exprt &rhs(condition.rhs());
  const typet &lhs_type(lhs.type());
  if(lhs_type != rhs.type())
    rhs = typecast_exprt(rhs, lhs_type);

  code_branch.cond() = condition;
  code_branch.cond().add_source_location() = location;
  const method_offsett label_number = numeric_cast_v<method_offsett>(number);
  code_branch.then_case() = code_gotot(label(std::to_string(label_number)));
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
  auto retvar = variable(arg0, 'a', address, NO_CAST);
  for(size_t idx = 0, idxlim = jsr_ret_targets.size(); idx != idxlim; ++idx)
  {
    irep_idt number = std::to_string(jsr_ret_targets[idx]);
    code_gotot g(label(number));
    g.add_source_location() = location;
    if(idx == idxlim - 1)
      c.move_to_operands(g);
    else
    {
      code_ifthenelset branch;
      auto address_ptr =
        from_integer(jsr_ret_targets[idx], unsignedbv_typet(64));
      address_ptr.type() = pointer_type(void_typet());
      branch.cond() = equal_exprt(retvar, address_ptr);
      branch.cond().add_source_location() = location;
      branch.then_case() = g;
      branch.add_source_location() = location;
      c.move_to_operands(branch);
    }
  }
  return c;
}

exprt java_bytecode_convert_methodt::convert_aload(
  const irep_idt &statement,
  const exprt::operandst &op) const
{
  const char &type_char = statement[0];
  const typecast_exprt pointer(op[0], java_array_type(type_char));

  dereference_exprt deref(pointer, pointer.type().subtype());
  deref.set(ID_java_member_access, true);

  const member_exprt data_ptr(
    deref, "data", pointer_type(java_type_from_char(type_char)));

  plus_exprt data_plus_offset(data_ptr, op[1], data_ptr.type());
  // tag it so it's easy to identify during instrumentation
  data_plus_offset.set(ID_java_array_access, true);
  const typet &element_type = data_ptr.type().subtype();
  const dereference_exprt element(data_plus_offset, element_type);
  return java_bytecode_promotion(element);
}

codet java_bytecode_convert_methodt::convert_store(
  const irep_idt &statement,
  const exprt &arg0,
  const exprt::operandst &op,
  const method_offsett address,
  const source_locationt &location)
{
  const exprt var = variable(arg0, statement[0], address, NO_CAST);
  const irep_idt &var_name = to_symbol_expr(var).get_identifier();

  exprt toassign = op[0];
  if('a' == statement[0] && toassign.type() != var.type())
    toassign = typecast_exprt(toassign, var.type());

  code_blockt block;

  save_stack_entries(
    "stack_store",
    toassign.type(),
    block,
    bytecode_write_typet::VARIABLE,
    var_name);
  code_assignt assign(var, toassign);
  assign.add_source_location() = location;
  block.move(assign);
  return block;
}

codet java_bytecode_convert_methodt::convert_astore(
  const irep_idt &statement,
  const exprt::operandst &op,
  const source_locationt &location)
{
  const char type_char = statement[0];
  const typecast_exprt pointer(op[0], java_array_type(type_char));

  dereference_exprt deref(pointer, pointer.type().subtype());
  deref.set(ID_java_member_access, true);

  const member_exprt data_ptr(
    deref, "data", pointer_type(java_type_from_char(type_char)));

  plus_exprt data_plus_offset(data_ptr, op[1], data_ptr.type());
  // tag it so it's easy to identify during instrumentation
  data_plus_offset.set(ID_java_array_access, true);
  const typet &element_type = data_ptr.type().subtype();
  const dereference_exprt element(data_plus_offset, element_type);

  code_blockt block;
  block.add_source_location() = location;

  save_stack_entries(
    "stack_astore", element_type, block, bytecode_write_typet::ARRAY_REF, "");

  code_assignt array_put(element, op[2]);
  array_put.add_source_location() = location;
  block.move(array_put);
  return block;
}

optionalt<exprt> java_bytecode_convert_methodt::convert_invoke_dynamic(
  const java_class_typet::java_lambda_method_handlest &lambda_method_handles,
  const source_locationt &location,
  const exprt &arg0)
{
  const java_method_typet &method_type = to_java_method_type(arg0.type());

  const optionalt<symbolt> &lambda_method_symbol = get_lambda_method_symbol(
    lambda_method_handles,
    method_type.get_int(ID_java_lambda_method_handle_index));
  if(lambda_method_symbol.has_value())
    debug() << "Converting invokedynamic for lambda: "
            << lambda_method_symbol.value().name << eom;
  else
    debug() << "Converting invokedynamic for lambda with unknown handle "
               "type"
            << eom;

  const java_method_typet::parameterst &parameters(method_type.parameters());

  pop(parameters.size());

  const typet &return_type = method_type.return_type();

  if(return_type.id() == ID_empty)
    return {};

  return zero_initializer(
    return_type, location, namespacet(symbol_table), get_message_handler());
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
      base_name = "this";
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
  bool threading_support)

{
  if(std::regex_match(
       id2string(class_symbol.name),
       std::regex(".*org\\.cprover\\.CProver.*")) &&
     cprover_methods_to_ignore.count(id2string(method.name)))
  {
    // Ignore these methods; fall back to the driver program's
    // stubbing behaviour.
    return;
  }

  java_bytecode_convert_methodt java_bytecode_convert_method(
    symbol_table,
    message_handler,
    max_array_length,
    throw_assertion_error,
    needed_lazy_methods,
    string_preprocess,
    class_hierarchy,
    threading_support);

  java_bytecode_convert_method(class_symbol, method);
}

/// Returns true iff method \p methodid from class \p classname is
/// a method inherited from a class (and not an interface!) from which
/// \p classname inherits, either directly or indirectly.
/// \param classname: class whose method is referenced
/// \param methodid: method basename
bool java_bytecode_convert_methodt::is_method_inherited(
  const irep_idt &classname,
  const irep_idt &methodid) const
{
  resolve_inherited_componentt::inherited_componentt inherited_method =
    get_inherited_component(
      classname,
      methodid,
      symbol_table,
      class_hierarchy,
      false);
  return inherited_method.is_valid();
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
  resolve_inherited_componentt::inherited_componentt inherited_method =
    get_inherited_component(
      class_identifier,
      component_name,
      symbol_table,
      class_hierarchy,
      true);

  INVARIANT(
    inherited_method.is_valid(), "static field should be in symbol table");

  return inherited_method.get_full_component_identifier();
}

/// Create temporary variables if a write instruction can have undesired side-
/// effects.
/// \param tmp_var_prefix: The prefix string to use for new temporary variables
/// \param tmp_var_type: The type of the temporary variable.
/// \param[out] block: The code block the assignment is added to if required.
/// \param write_type: The enumeration type of the write instruction.
/// \param identifier: The identifier of the symbol in the write instruction.
void java_bytecode_convert_methodt::save_stack_entries(
  const std::string &tmp_var_prefix,
  const typet &tmp_var_type,
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
      create_stack_tmp_var(tmp_var_prefix, tmp_var_type, block, stack_entry);
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
  block.copy_to_operands(code_assignt(tmp_var, stack_entry));
  stack_entry=tmp_var;
}

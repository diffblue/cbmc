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
#include "java_string_library_preprocess.h"
#include "java_types.h"
#include "java_utils.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string2int.h>

#include <linking/zero_initializer.h>

#include <goto-programs/cfg.h>
#include <goto-programs/remove_exceptions.h>
#include <goto-programs/class_hierarchy.h>
#include <goto-programs/resolve_concrete_function_call.h>
#include <analyses/cfg_dominators.h>

#include <limits>
#include <algorithm>
#include <functional>
#include <unordered_set>
#include <regex>

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
void assign_parameter_names(
  code_typet &ftype,
  const irep_idt &name_prefix,
  symbol_tablet &symbol_table)
{
  code_typet::parameterst &parameters=ftype.parameters();

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

static irep_idt strip_java_namespace_prefix(const irep_idt to_strip)
{
  const std::string to_strip_str=id2string(to_strip);
  const std::string prefix="java::";

  PRECONDITION(has_prefix(to_strip_str, prefix));
  return to_strip_str.substr(prefix.size(), std::string::npos);
}

// name contains <init> or <clinit>
bool java_bytecode_convert_methodt::is_constructor(
  const class_typet::methodt &method)
{
  const std::string &name(id2string(method.get_name()));
  const std::string::size_type &npos(std::string::npos);
  return npos!=name.find("<init>") || npos!=name.find("<clinit>");
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

/// This creates a method symbol in the symtab, but doesn't actually perform
/// method conversion just yet. The caller should call
/// java_bytecode_convert_method later to give the symbol/method a body.
/// \par parameters: `class_symbol`: class this method belongs to
/// `method_identifier`: fully qualified method name, including type descriptor
///   (e.g. "x.y.z.f:(I)")
/// `m`: parsed method object to convert
/// `symbol_table`: global symbol table (will be modified)
void java_bytecode_convert_method_lazy(
  const symbolt &class_symbol,
  const irep_idt &method_identifier,
  const java_bytecode_parse_treet::methodt &m,
  symbol_tablet &symbol_table)
{
  symbolt method_symbol;
  typet member_type;
  if(m.signature.has_value())
  {
#ifdef DEBUG
    std::cout << "method " << m.name
              << " has signature " << m.signature.value() << "\n";
#endif
    member_type=java_type_from_string(
      m.signature.value(),
      id2string(class_symbol.name));
    INVARIANT(member_type.id()==ID_code, "Must be code type");
  }
  else
    member_type=java_type_from_string(m.descriptor);

  method_symbol.name=method_identifier;
  method_symbol.base_name=m.base_name;
  method_symbol.mode=ID_java;
  method_symbol.location=m.source_location;
  method_symbol.location.set_function(method_identifier);
  if(m.is_public)
    member_type.set(ID_access, ID_public);
  else if(m.is_protected)
    member_type.set(ID_access, ID_protected);
  else if(m.is_private)
    member_type.set(ID_access, ID_private);
  else
    member_type.set(ID_access, ID_default);

  if(method_symbol.base_name=="<init>")
  {
    method_symbol.pretty_name=
      id2string(class_symbol.pretty_name)+"."+
      id2string(class_symbol.base_name)+"()";
    member_type.set(ID_constructor, true);
  }
  else
    method_symbol.pretty_name=
      id2string(class_symbol.pretty_name)+"."+
      id2string(m.base_name)+"()";

  // do we need to add 'this' as a parameter?
  if(!m.is_static)
  {
    code_typet &code_type=to_code_type(member_type);
    code_typet::parameterst &parameters=code_type.parameters();
    code_typet::parametert this_p;
    const reference_typet object_ref_type=
      java_reference_type(symbol_typet(class_symbol.name));
    this_p.type()=object_ref_type;
    this_p.set_this();
    parameters.insert(parameters.begin(), this_p);
  }

  method_symbol.type=member_type;
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

  const symbolt &old_sym=*symbol_table.lookup(method_identifier);

  // Obtain a std::vector of code_typet::parametert objects from the
  // (function) type of the symbol
  typet member_type=old_sym.type;
  code_typet &code_type=to_code_type(member_type);
  method_return_type=code_type.return_type();
  code_typet::parameterst &parameters=code_type.parameters();

  // Determine the number of local variable slots used by the JVM to maintan the
  // formal parameters
  slots_for_parameters=java_method_parameter_slots(code_type);

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

  const bool is_virtual=!m.is_static && !m.is_final;

  // Construct a methodt, which lives within the class type; this object is
  // never used for anything useful and could be removed
  class_typet::methodt method;
  method.set_base_name(m.base_name);
  method.set_name(method_identifier);
  method.set(ID_abstract, m.is_abstract);
  method.set(ID_is_virtual, is_virtual);
  method.type()=member_type;
  if(is_constructor(method))
    method.set(ID_constructor, true);

  // we add the symbol for the method
  symbolt method_symbol;
  method_symbol.name=method.get_name();
  method_symbol.base_name=method.get_base_name();
  method_symbol.mode=ID_java;
  method_symbol.location=m.source_location;
  method_symbol.location.set_function(method_identifier);

  // Set up the pretty name for the method entry in the symbol table.
  // The pretty name of a constructor includes the base name of the class
  // instead of the internal method name "<init>". For regular methods, it's
  // just the base name of the method.
  if(method.get_base_name()=="<init>")
    method_symbol.pretty_name=id2string(class_symbol.pretty_name)+"."+
                              id2string(class_symbol.base_name)+"()";
  else
    method_symbol.pretty_name=id2string(class_symbol.pretty_name)+"."+
                              id2string(method.get_base_name())+"()";

  method_symbol.type=member_type;
  if(is_constructor(method))
    method_symbol.type.set(ID_constructor, true);

  current_method=method_symbol.name;
  method_has_this=code_type.has_this();
  if((!m.is_abstract) && (!m.is_native))
    method_symbol.value=convert_instructions(m, code_type, method_symbol.name);

  // Replace the existing stub symbol with the real deal:
  const auto s_it=symbol_table.symbols.find(method.get_name());
  INVARIANT(
    s_it!=symbol_table.symbols.end(),
    "the symbol was there earlier on this function; it must be there now");
  symbol_table.erase(s_it);

  // Insert the method symbol in the symbol table
  symbol_table.add(method_symbol);
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

  exprt pointer2=
    typecast_exprt(pointer, java_reference_type(class_type));

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
  unsigned address_start,
  unsigned address_limit,
  unsigned next_block_start_address)
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
  unsigned address_start,
  unsigned address_limit,
  unsigned next_block_start_address,
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
  unsigned findlim_block_start_address=
    findlim==tree.branch_addresses.end() ?
    next_block_start_address :
    (*findlim);

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
  std::string new_label_str=as_string(child_label_name);
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
  unsigned pc,
  const exprt &e,
  std::map<irep_idt, java_bytecode_convert_methodt::variablet> &result)
{
  if(e.id()==ID_symbol)
  {
    const auto &symexpr=to_symbol_expr(e);
    auto findit=
      result.insert({ // NOLINT(whitespace/braces)
        symexpr.get_identifier(),
        java_bytecode_convert_methodt::variablet()});
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

/// See above
/// \par parameters: `se`: Symbol expression referring to a static field
/// `basename`: The static field's basename
/// \return Creates a symbol table entry for the static field if one doesn't
///   exist already.
void java_bytecode_convert_methodt::check_static_field_stub(
  const symbol_exprt &symbol_expr,
  const irep_idt &basename)
{
  const auto &id=symbol_expr.get_identifier();
  if(symbol_table.symbols.find(id)==symbol_table.symbols.end())
  {
    // Create a stub, to be overwritten if/when the real class is loaded.
    symbolt new_symbol;
    new_symbol.is_static_lifetime=true;
    new_symbol.is_lvalue=true;
    new_symbol.is_state_var=true;
    new_symbol.name=id;
    new_symbol.base_name=basename;
    new_symbol.type=symbol_expr.type();
    new_symbol.pretty_name=new_symbol.name;
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;
    new_symbol.value.make_nil();
    symbol_table.add(new_symbol);
  }
}

/// Determine whether a `new` or static access against `classname` should be
/// prefixed with a static initialization check.
/// \param classname: Class name
/// \return Returns true if the given class or one of its parents has a static
///   initializer
bool java_bytecode_convert_methodt::class_needs_clinit(
  const irep_idt &classname)
{
  auto findit_any=any_superclass_has_clinit_method.insert({classname, false});
  if(!findit_any.second)
    return findit_any.first->second;

  auto findit_here=class_has_clinit_method.insert({classname, false});
  if(findit_here.second)
  {
    const irep_idt &clinit_name=id2string(classname)+".<clinit>:()V";
    findit_here.first->second=symbol_table.symbols.count(clinit_name);
  }
  if(findit_here.first->second)
  {
    findit_any.first->second=true;
    return true;
  }
  symbol_tablet::opt_const_symbol_reft maybe_symbol=
    symbol_table.lookup(classname);
  // Stub class?
  if(!maybe_symbol)
  {
    warning() << "SKIPPED: " << classname << eom;
    return false;
  }
  const symbolt &class_symbol=*maybe_symbol;
  for(const auto &base : to_class_type(class_symbol.type).bases())
  {
    if(class_needs_clinit(to_symbol_type(base.type()).get_identifier()))
    {
      findit_any.first->second=true;
      return true;
    }
  }
  return false;
}

/// Create a ::clinit_wrapper the first time a static initializer might be
/// called. The wrapper method checks whether static init has already taken
/// place, calls the actual <clinit> method if not, and initializes super-
/// classes and interfaces.
/// \param classname: Class name
/// \return Returns a symbol_exprt pointing to the given class' clinit wrapper
///   if one is required, or nil otherwise.
exprt java_bytecode_convert_methodt::get_or_create_clinit_wrapper(
  const irep_idt &classname)
{
  if(!class_needs_clinit(classname))
    return static_cast<const exprt &>(get_nil_irep());

  const irep_idt &clinit_wrapper_name=
    id2string(classname)+"::clinit_wrapper";
  auto findit=symbol_table.symbols.find(clinit_wrapper_name);
  if(findit!=symbol_table.symbols.end())
    return findit->second.symbol_expr();

  // Create the wrapper now:
  const irep_idt &already_run_name=
    id2string(classname)+"::clinit_already_run";
  symbolt already_run_symbol;
  already_run_symbol.name=already_run_name;
  already_run_symbol.pretty_name=already_run_name;
  already_run_symbol.base_name="clinit_already_run";
  already_run_symbol.type=bool_typet();
  already_run_symbol.value=false_exprt();
  already_run_symbol.is_lvalue=true;
  already_run_symbol.is_state_var=true;
  already_run_symbol.is_static_lifetime=true;
  already_run_symbol.mode=ID_java;
  symbol_table.add(already_run_symbol);

  equal_exprt check_already_run(
    already_run_symbol.symbol_expr(),
    false_exprt());

  code_ifthenelset wrapper_body;
  wrapper_body.cond()=check_already_run;
  code_blockt init_body;
  // Note already-run is set *before* calling clinit, in order to prevent
  // recursion in clinit methods.
  code_assignt set_already_run(already_run_symbol.symbol_expr(), true_exprt());
  init_body.move_to_operands(set_already_run);
  const irep_idt &real_clinit_name=id2string(classname)+".<clinit>:()V";
  const symbolt &class_symbol=*symbol_table.lookup(classname);

  auto findsymit=symbol_table.symbols.find(real_clinit_name);
  if(findsymit!=symbol_table.symbols.end())
  {
    code_function_callt call_real_init;
    call_real_init.function()=findsymit->second.symbol_expr();
    init_body.move_to_operands(call_real_init);
  }

  for(const auto &base : to_class_type(class_symbol.type).bases())
  {
    const auto base_name=to_symbol_type(base.type()).get_identifier();
    exprt base_init_routine=get_or_create_clinit_wrapper(base_name);
    if(base_init_routine.is_nil())
      continue;
    code_function_callt call_base;
    call_base.function()=base_init_routine;
    init_body.move_to_operands(call_base);
  }

  wrapper_body.then_case()=init_body;

  symbolt wrapper_method_symbol;
  code_typet wrapper_method_type;
  wrapper_method_type.return_type()=void_typet();
  wrapper_method_symbol.name=clinit_wrapper_name;
  wrapper_method_symbol.pretty_name=clinit_wrapper_name;
  wrapper_method_symbol.base_name="clinit_wrapper";
  wrapper_method_symbol.type=wrapper_method_type;
  wrapper_method_symbol.value=wrapper_body;
  wrapper_method_symbol.mode=ID_java;
  symbol_table.add(wrapper_method_symbol);
  return wrapper_method_symbol.symbol_expr();
}

/// Each static access to classname should be prefixed with a check for
/// necessary static init; this returns a call implementing that check.
/// \param classname: Class name
/// \return Returns a function call to the given class' static initializer
///   wrapper if one is needed, or a skip instruction otherwise.
codet java_bytecode_convert_methodt::get_clinit_call(
  const irep_idt &classname)
{
  exprt callee=get_or_create_clinit_wrapper(classname);
  if(callee.is_nil())
    return code_skipt();
  code_function_callt ret;
  ret.function()=callee;
  return ret;
}

static unsigned get_bytecode_type_width(const typet &ty)
{
  if(ty.id()==ID_pointer)
    return 32;
  return ty.get_unsigned_int(ID_width);
}

codet java_bytecode_convert_methodt::convert_instructions(
  const methodt &method,
  const code_typet &method_type,
  const irep_idt &method_name)
{
  const instructionst &instructions=method.instructions;

  // Run a worklist algorithm, assuming that the bytecode has not
  // been tampered with. See "Leroy, X. (2003). Java bytecode
  // verification: algorithms and formalizations. Journal of Automated
  // Reasoning, 30(3-4), 235-269." for a more complete treatment.

  // first pass: get targets and map addresses to instructions

  address_mapt address_map;
  std::set<unsigned> targets;

  std::vector<unsigned> jsr_ret_targets;
  std::vector<instructionst::const_iterator> ret_instructions;

  for(instructionst::const_iterator
      i_it=instructions.begin();
      i_it!=instructions.end();
      i_it++)
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
       i_it->statement=="invokeinterface")
    {
      // find the corresponding try-catch blocks and add the handlers
      // to the targets
      for(const auto &exception_row : method.exception_table)
      {
        if(i_it->address>=exception_row.start_pc &&
           i_it->address<exception_row.end_pc)
        {
          a_entry.first->second.successors.push_back(
            exception_row.handler_pc);
          targets.insert(exception_row.handler_pc);
        }
      }
    }

    if(i_it->statement=="goto" ||
       i_it->statement==patternt("if_?cmp??") ||
       i_it->statement==patternt("if??") ||
       i_it->statement=="ifnonnull" ||
       i_it->statement=="ifnull" ||
       i_it->statement=="jsr" ||
       i_it->statement=="jsr_w")
    {
      assert(!i_it->args.empty());

      unsigned target;
      bool ret=to_unsigned_integer(to_constant_expr(i_it->args[0]), target);
      DATA_INVARIANT(!ret, "target expected to be unsigned integer");
      targets.insert(target);

      a_entry.first->second.successors.push_back(target);

      if(i_it->statement=="jsr" ||
         i_it->statement=="jsr_w")
      {
        instructionst::const_iterator next=i_it+1;
        assert(
          next!=instructions.end() &&
          "jsr without valid return address?");
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

  // Draw edges from every `ret` to every `jsr` successor. Could do better with
  // flow analysis to distinguish multiple subroutines within the same function.
  for(const auto retinst : ret_instructions)
  {
    auto &a_entry=address_map.at(retinst->address);
    a_entry.successors.insert(
      a_entry.successors.end(),
      jsr_ret_targets.begin(),
      jsr_ret_targets.end());
  }

  for(const auto &address : address_map)
  {
    for(unsigned s : address.second.successors)
    {
      address_mapt::iterator a_it=address_map.find(s);
      assert(a_it!=address_map.end());

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

  std::set<unsigned> working_set;

  if(!instructions.empty())
    working_set.insert(instructions.front().address);

  while(!working_set.empty())
  {
    std::set<unsigned>::iterator cur=working_set.begin();
    address_mapt::iterator a_it=address_map.find(*cur);
    assert(a_it!=address_map.end());
    unsigned cur_pc=*cur;
    working_set.erase(cur);

    if(a_it->second.done)
      continue;
    working_set
      .insert(a_it->second.successors.begin(), a_it->second.successors.end());

    instructionst::const_iterator i_it=a_it->second.source;
    stack.swap(a_it->second.stack);
    a_it->second.stack.clear();
    codet &c=a_it->second.code;

    assert(
      stack.empty() ||
      a_it->second.predecessors.size()<=1 ||
      has_prefix(
        stack.front().get_string(ID_C_base_name),
        "$stack"));

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
        if(catch_type!=typet() || it->catch_type==symbol_typet())
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
      assert(op.size()==1 && results.size()==1);

      side_effect_expr_throwt throw_expr;
      throw_expr.add_source_location()=i_it->source_location;
      throw_expr.copy_to_operands(op[0]);
      c=code_expressiont(throw_expr);
      results[0]=op[0];
    }
    else if(statement=="checkcast")
    {
      // checkcast throws an exception in case a cast of object
      // on stack to given type fails.
      // The stack isn't modified.
      assert(op.size()==1 && results.size()==1);
      binary_predicate_exprt check(op[0], ID_java_instanceof, arg0);
      code_assertt assert_class(check);
      assert_class.add_source_location().set_comment("Dynamic cast check");
      assert_class.add_source_location().set_property_class("bad-dynamic-cast");
      // we add this assert such that we can recognise it
      // during the instrumentation phase
      c=std::move(assert_class);
      results[0]=op[0];
    }
    else if(statement=="invokedynamic")
    {
      // not used in Java
      code_typet &code_type=to_code_type(arg0.type());
      const code_typet::parameterst &parameters(code_type.parameters());

      pop(parameters.size());

      const typet &return_type=code_type.return_type();

      if(return_type.id()!=ID_empty)
      {
        results.resize(1);
        results[0]=
          zero_initializer(
            return_type,
            i_it->source_location,
            namespacet(symbol_table),
            get_message_handler());
      }
    }
    // replace calls to CProver.assume
    else if(statement=="invokestatic" &&
            id2string(arg0.get(ID_identifier))==
            "java::org.cprover.CProver.assume:(Z)V")
    {
      const code_typet &code_type=to_code_type(arg0.type());
      // sanity check: function has the right number of args
      assert(code_type.parameters().size()==1);

      exprt operand = pop(1)[0];
      // we may need to adjust the type of the argument
      if(operand.type()!=bool_typet())
        operand.make_typecast(bool_typet());

      c=code_assumet(operand);
      source_locationt loc=i_it->source_location;
      loc.set_function(method_id);
      c.add_source_location()=loc;
    }
    else if(statement=="invokeinterface" ||
            statement=="invokespecial" ||
            statement=="invokevirtual" ||
            statement=="invokestatic")
    {
      const bool use_this(statement!="invokestatic");
      const bool is_virtual(
        statement=="invokevirtual" || statement=="invokeinterface");

      code_typet &code_type=to_code_type(arg0.type());
      code_typet::parameterst &parameters(code_type.parameters());

      if(use_this)
      {
        if(parameters.empty() || !parameters[0].get_this())
        {
          irep_idt classname=arg0.get(ID_C_class);
          typet thistype=symbol_typet(classname);
          // Note invokespecial is used for super-method calls as well as
          // constructors.
          if(statement=="invokespecial")
          {
            if(as_string(arg0.get(ID_identifier))
               .find("<init>")!=std::string::npos)
            {
              if(lazy_methods)
                lazy_methods->add_needed_class(classname);
              code_type.set(ID_constructor, true);
            }
            else
              code_type.set(ID_java_super_method_call, true);
          }
          reference_typet object_ref_type=java_reference_type(thistype);
          code_typet::parametert this_p(object_ref_type);
          this_p.set_this();
          this_p.set_base_name("this");
          parameters.insert(parameters.begin(), this_p);
        }
      }

      code_function_callt call;
      source_locationt loc=i_it->source_location;
      loc.set_function(method_id);

      call.add_source_location()=loc;
      call.arguments()=pop(parameters.size());

      // double-check a bit
      if(use_this)
      {
        const exprt &this_arg=call.arguments().front();
        assert(this_arg.type().id()==ID_pointer);
      }

      // do some type adjustment for the arguments,
      // as Java promotes arguments
      // Also cast pointers since intermediate locals
      // can be void*.

      for(std::size_t i=0; i<parameters.size(); i++)
      {
        const typet &type=parameters[i].type();
        if(type==java_boolean_type() ||
           type==java_char_type() ||
           type==java_byte_type() ||
           type==java_short_type() ||
           type.id()==ID_pointer)
        {
          assert(i<call.arguments().size());
          if(type!=call.arguments()[i].type())
            call.arguments()[i].make_typecast(type);
        }
      }

      // do some type adjustment for return values

      const typet &return_type=code_type.return_type();

      if(return_type.id()!=ID_empty)
      {
        // return types are promoted in Java
        call.lhs()=tmp_variable("return", return_type);
        exprt promoted=java_bytecode_promotion(call.lhs());
        results.resize(1);
        results[0]=promoted;
      }

      assert(arg0.id()==ID_virtual_function);

      // If we don't have a definition for the called symbol, and we won't
      // inherit a definition from a super-class, we create a new symbol and
      // insert it in the symbol table. The name and type of the method are
      // derived from the information we have in the call.
      // We fix the access attribute to ID_public, because of the following
      // reasons:
      // - We don't know the orignal access attribute and since the .class file
      //   unavailable, we have no way to know.
      // - Whatever it was, we assume that the bytecode we are translating
      //   compiles correctly, so such a method has to be accessible from this
      //   method.
      // - We will never generate code that calls that method unless we
      //   translate bytecode that calls that method. As a result we will never
      //   generate code that may wrongly assume that such a method is
      //   accessible if we assume that its access attribute is "more
      //   accessible" than it actually is.
      irep_idt id=arg0.get(ID_identifier);
      if(symbol_table.symbols.find(id)==symbol_table.symbols.end() &&
         !(is_virtual && is_method_inherited(arg0.get(ID_C_class), arg0.get(ID_component_name))))
      {
        symbolt symbol;
        symbol.name=id;
        symbol.base_name=arg0.get(ID_C_base_name);
        symbol.pretty_name=
          id2string(arg0.get(ID_C_class)).substr(6)+"."+
          id2string(symbol.base_name)+"()";
        symbol.type=arg0.type();
        symbol.type.set(ID_access, ID_public);
        symbol.value.make_nil();
        symbol.mode=ID_java;
        assign_parameter_names(
          to_code_type(symbol.type),
          symbol.name,
          symbol_table);

        debug()
          << "Generating codet:  new opaque symbol: method '"
          << symbol.name << "'" << eom;
        symbol_table.add(symbol);
      }

      if(is_virtual)
      {
        // dynamic binding
        assert(use_this);
        assert(!call.arguments().empty());
        call.function()=arg0;
        // Populate needed methods later,
        // once we know what object types can exist.
      }
      else
      {
        // static binding
        call.function()=symbol_exprt(arg0.get(ID_identifier), arg0.type());
        if(lazy_methods)
        {
          lazy_methods->add_needed_method(arg0.get(ID_identifier));
          // Calling a static method causes static initialization:
          lazy_methods->add_needed_class(arg0.get(ID_C_class));
        }
      }

      call.function().add_source_location()=loc;

      // Replacing call if it is a function of the Character library,
      // returning the same call otherwise
      c=string_preprocess.replace_character_call(call);

      if(!use_this)
      {
        codet clinit_call=get_clinit_call(arg0.get(ID_C_class));
        if(clinit_call.get_statement()!=ID_skip)
        {
          code_blockt ret_block;
          ret_block.move_to_operands(clinit_call);
          ret_block.move_to_operands(c);
          c=std::move(ret_block);
        }
      }
    }
    else if(statement=="return")
    {
      assert(op.empty() && results.empty());
      c=code_returnt();
    }
    else if(statement==patternt("?return"))
    {
      // Return types are promoted in java, so this might need
      // conversion.
      assert(op.size()==1 && results.empty());
      exprt r=op[0];
      if(r.type()!=method_return_type)
        r=typecast_exprt(r, method_return_type);
      c=code_returnt(r);
    }
    else if(statement==patternt("?astore"))
    {
      assert(op.size()==3 && results.empty());

      char type_char=statement[0];

      exprt pointer=
        typecast_exprt(op[0], java_array_type(type_char));

      dereference_exprt deref(pointer, pointer.type().subtype());
      deref.set(ID_java_member_access, true);

      const member_exprt data_ptr(
        deref,
        "data",
        pointer_type(java_type_from_char(type_char)));

      plus_exprt data_plus_offset(data_ptr, op[1], data_ptr.type());
      // tag it so it's easy to identify during instrumentation
      data_plus_offset.set(ID_java_array_access, true);
      typet element_type=data_ptr.type().subtype();
      const dereference_exprt element(data_plus_offset, element_type);

      code_blockt block;
      block.add_source_location()=i_it->source_location;

      save_stack_entries(
        "stack_astore",
        element_type,
        block,
        bytecode_write_typet::ARRAY_REF,
        "");

      code_assignt array_put(element, op[2]);
      array_put.add_source_location()=i_it->source_location;
      block.move_to_operands(array_put);
      c=block;
    }
    else if(statement==patternt("?store"))
    {
      // store value into some local variable
      assert(op.size()==1 && results.empty());

      exprt var=
        variable(arg0, statement[0], i_it->address, NO_CAST);
      const irep_idt &var_name=to_symbol_expr(var).get_identifier();

      exprt toassign=op[0];
      if('a'==statement[0] && toassign.type()!=var.type())
        toassign=typecast_exprt(toassign, var.type());

      code_blockt block;

      save_stack_entries(
        "stack_store",
        toassign.type(),
        block,
        bytecode_write_typet::VARIABLE,
        var_name);
      code_assignt assign(var, toassign);
      assign.add_source_location()=i_it->source_location;
      block.copy_to_operands(assign);
      c=block;
    }
    else if(statement==patternt("?aload"))
    {
      assert(op.size()==2 && results.size()==1);

      char type_char=statement[0];

      exprt pointer=
        typecast_exprt(op[0], java_array_type(type_char));

      dereference_exprt deref(pointer, pointer.type().subtype());
      deref.set(ID_java_member_access, true);

      const member_exprt data_ptr(
        deref,
        "data",
        pointer_type(java_type_from_char(type_char)));

      plus_exprt data_plus_offset(data_ptr, op[1], data_ptr.type());
      // tag it so it's easy to identify during instrumentation
      data_plus_offset.set(ID_java_array_access, true);
      typet element_type=data_ptr.type().subtype();
      dereference_exprt element(data_plus_offset, element_type);
      results[0]=java_bytecode_promotion(element);
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
      assert(op.empty() && results.size()==1);

      // 1) Pushing a String causes a reference to a java.lang.String object
      // to be constructed and pushed onto the operand stack.

      // 2) Pushing an int or a float causes a primitive value to be pushed
      // onto the stack.

      // 3) Pushing a Class constant causes a reference to a java.lang.Class
      // to be pushed onto the operand stack

      if(arg0.id()==ID_java_string_literal)
      {
        // these need to be references to java.lang.String
        results[0]=arg0;
        symbol_typet string_type("java::java.lang.String");
        results[0].type()=java_reference_type(string_type);
      }
      else if(arg0.id()==ID_type)
      {
        irep_idt class_id=arg0.type().get(ID_identifier);
        symbol_typet java_lang_Class("java::java.lang.Class");
        symbol_exprt symbol_expr(
          id2string(class_id)+"@class_model",
          java_lang_Class);
        address_of_exprt address_of_expr(symbol_expr);
        results[0]=address_of_expr;
      }
      else if(arg0.id()==ID_constant)
      {
        results[0]=arg0;
      }
      else
      {
        error() << "unexpected ldc argument" << eom;
        throw 0;
      }
    }
    else if(statement=="goto" || statement=="goto_w")
    {
      assert(op.empty() && results.empty());
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg0), number);
      INVARIANT(!ret, "goto argument should be an integer");
      code_gotot code_goto(label(integer2string(number)));
      c=code_goto;
    }
    else if(statement=="jsr" || statement=="jsr_w")
    {
      // As 'goto', except we must also push the subroutine return address:
      assert(op.empty() && results.size()==1);
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
      assert(op.empty() && results.empty());
      c=code_blockt();
      auto retvar=variable(arg0, 'a', i_it->address, NO_CAST);
      assert(!jsr_ret_targets.empty());
      for(size_t idx=0, idxlim=jsr_ret_targets.size(); idx!=idxlim; ++idx)
      {
        irep_idt number=std::to_string(jsr_ret_targets[idx]);
        code_gotot g(label(number));
        g.add_source_location()=i_it->source_location;
        if(idx==idxlim-1)
          c.move_to_operands(g);
        else
        {
          code_ifthenelset branch;
          auto address_ptr=
            from_integer(
              jsr_ret_targets[idx],
              unsignedbv_typet(64));
          address_ptr.type()=pointer_type(void_typet());
          branch.cond()=equal_exprt(retvar, address_ptr);
          branch.cond().add_source_location()=i_it->source_location;
          branch.then_case()=g;
          branch.add_source_location()=i_it->source_location;
          c.move_to_operands(branch);
        }
      }
    }
    else if(statement=="iconst_m1")
    {
      assert(results.size()==1);
      results[0]=from_integer(-1, java_int_type());
    }
    else if(statement==patternt("?const"))
    {
      assert(results.size()==1);

      const char type_char=statement[0];
      const bool is_double('d'==type_char);
      const bool is_float('f'==type_char);

      if(is_double || is_float)
      {
        const ieee_float_spect spec(
          is_float?ieee_float_spect::single_precision():
          ieee_float_spect::double_precision());

        ieee_floatt value(spec);
        if(arg0.type().id()!=ID_floatbv)
        {
          mp_integer number;
          bool ret=to_integer(to_constant_expr(arg0), number);
          DATA_INVARIANT(!ret, "failed to convert constant");
          value.from_integer(number);
        }
        else
          value.from_expr(to_constant_expr(arg0));

        results[0]=value.to_expr();
      }
      else
      {
        mp_integer value;
        bool ret=to_integer(to_constant_expr(arg0), value);
        DATA_INVARIANT(!ret, "failed to convert constant");
        const typet type=java_type_from_char(statement[0]);
        results[0]=from_integer(value, type);
      }
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
      assert(op.size()==2 && results.empty());
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg0), number);
      INVARIANT(!ret, "if_?cmp?? argument should be an integer");

      code_ifthenelset code_branch;
      const irep_idt cmp_op=get_if_cmp_operator(statement);

      binary_relation_exprt condition(op[0], cmp_op, op[1]);

      exprt &lhs(condition.lhs());
      exprt &rhs(condition.rhs());
      const typet &lhs_type(lhs.type());
      if(lhs_type!=rhs.type())
        rhs=typecast_exprt(rhs, lhs_type);

      code_branch.cond()=condition;
      code_branch.cond().add_source_location()=i_it->source_location;
      code_branch.then_case()=code_gotot(label(integer2string(number)));
      code_branch.then_case().add_source_location()=
        address_map.at(integer2unsigned(number)).source->source_location;
      code_branch.add_source_location()=i_it->source_location;

      c=code_branch;
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

      assert(op.size()==1 && results.empty());
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg0), number);
      INVARIANT(!ret, "if?? argument should be an integer");

      code_ifthenelset code_branch;
      code_branch.cond()=
        binary_relation_exprt(op[0], id, from_integer(0, op[0].type()));
      code_branch.cond().add_source_location()=i_it->source_location;
      code_branch.cond().add_source_location().set_function(method_id);
      code_branch.then_case()=code_gotot(label(integer2string(number)));
      code_branch.then_case().add_source_location()=
        address_map.at(integer2unsigned(number)).source->source_location;
      code_branch.then_case().add_source_location().set_function(method_id);
      code_branch.add_source_location()=i_it->source_location;
      code_branch.add_source_location().set_function(method_id);

      c=code_branch;
    }
    else if(statement==patternt("ifnonnull"))
    {
      assert(op.size()==1 && results.empty());
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg0), number);
      INVARIANT(!ret, "ifnonnull argument should be an integer");
      code_ifthenelset code_branch;
      const typecast_exprt lhs(op[0], java_reference_type(empty_typet()));
      const exprt rhs(null_pointer_exprt(to_pointer_type(lhs.type())));
      code_branch.cond()=binary_relation_exprt(lhs, ID_notequal, rhs);
      code_branch.then_case()=code_gotot(label(integer2string(number)));
      code_branch.then_case().add_source_location()=
        address_map.at(integer2unsigned(number)).source->source_location;
      code_branch.add_source_location()=i_it->source_location;

      c=code_branch;
    }
    else if(statement==patternt("ifnull"))
    {
      assert(op.size()==1 && results.empty());
      mp_integer number;
      bool ret=to_integer(to_constant_expr(arg0), number);
      INVARIANT(!ret, "ifnull argument should be an integer");
      code_ifthenelset code_branch;
      const typecast_exprt lhs(op[0], java_reference_type(empty_typet()));
      const exprt rhs(null_pointer_exprt(to_pointer_type(lhs.type())));
      code_branch.cond()=binary_relation_exprt(lhs, ID_equal, rhs);
      code_branch.then_case()=code_gotot(label(integer2string(number)));
      code_branch.then_case().add_source_location()=
        address_map.at(integer2unsigned(number)).source->source_location;
      code_branch.add_source_location()=i_it->source_location;

      c=code_branch;
    }
    else if(statement=="iinc")
    {
      code_blockt block;
      block.add_source_location()=i_it->source_location;
      // search variable on stack
      const exprt &locvar=variable(arg0, 'i', i_it->address, NO_CAST);
      save_stack_entries(
        "stack_iinc",
        java_int_type(),
        block,
        bytecode_write_typet::VARIABLE,
        to_symbol_expr(locvar).get_identifier());

      code_assignt code_assign;
      code_assign.lhs()=
        variable(arg0, 'i', i_it->address, NO_CAST);
      exprt arg1_int_type=arg1;
      if(arg1.type()!=java_int_type())
        arg1_int_type.make_typecast(java_int_type());
      code_assign.rhs()=plus_exprt(
        variable(arg0, 'i', i_it->address, CAST_AS_NEEDED),
        arg1_int_type);
      block.copy_to_operands(code_assign);
      c=block;
    }
    else if(statement==patternt("?xor"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=bitxor_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?or"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=bitor_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?and"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=bitand_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?shl"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=shl_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?shr"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=ashr_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?ushr"))
    {
      assert(op.size()==2 && results.size()==1);
      const typet type=java_type_from_char(statement[0]);

      const std::size_t width=type.get_size_t(ID_width);
      typet target=unsignedbv_typet(width);

      exprt lhs=op[0];
      if(lhs.type()!=target)
        lhs.make_typecast(target);
      exprt rhs=op[1];
      if(rhs.type()!=target)
        rhs.make_typecast(target);

      results[0]=lshr_exprt(lhs, rhs);
      if(results[0].type()!=op[0].type())
        results[0].make_typecast(op[0].type());
    }
    else if(statement==patternt("?add"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=plus_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?sub"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=minus_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?div"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=div_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?mul"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=mult_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?neg"))
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=unary_minus_exprt(op[0], op[0].type());
    }
    else if(statement==patternt("?rem"))
    {
      assert(op.size()==2 && results.size()==1);
      if(statement=="frem" || statement=="drem")
        results[0]=rem_exprt(op[0], op[1]);
      else
        results[0]=mod_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?cmp"))
    {
      assert(op.size()==2 && results.size()==1);

      // The integer result on the stack is:
      //  0 if op[0] equals op[1]
      // -1 if op[0] is less than op[1]
      //  1 if op[0] is greater than op[1]

      const typet t=java_int_type();
      exprt one=from_integer(1, t);
      exprt minus_one=from_integer(-1, t);

      if_exprt greater=if_exprt(
        binary_relation_exprt(op[0], ID_gt, op[1]),
        one,
        minus_one);

      results[0]=
        if_exprt(
          binary_relation_exprt(op[0], ID_equal, op[1]),
          from_integer(0, t),
          greater);
    }
    else if(statement==patternt("?cmp?"))
    {
      assert(op.size()==2 && results.size()==1);
      const floatbv_typet type(
        to_floatbv_type(java_type_from_char(statement[0])));
      const ieee_float_spect spec(type);
      const ieee_floatt nan(ieee_floatt::NaN(spec));
      const constant_exprt nan_expr(nan.to_expr());
      const int nan_value(statement[4]=='l' ? -1 : 1);
      const typet result_type(java_int_type());
      const exprt nan_result(from_integer(nan_value, result_type));

      // (value1 == NaN || value2 == NaN) ?
      //   nan_value : value1  < value2 ? -1 : value2 < value1  1 ? 1 : 0;
      // (value1 == NaN || value2 == NaN) ?
      //   nan_value : value1 == value2 ? 0  : value1 < value2 -1 ? 1 : 0;

      exprt nan_op0=ieee_float_equal_exprt(nan_expr, op[0]);
      exprt nan_op1=ieee_float_equal_exprt(nan_expr, op[1]);
      exprt one=from_integer(1, result_type);
      exprt minus_one=from_integer(-1, result_type);
      results[0]=
        if_exprt(
          or_exprt(nan_op0, nan_op1),
          nan_result,
          if_exprt(
            ieee_float_equal_exprt(op[0], op[1]),
            from_integer(0, result_type),
            if_exprt(
              binary_relation_exprt(op[0], ID_lt, op[1]),
              minus_one,
              one)));
    }
    else if(statement==patternt("?cmpl"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=binary_relation_exprt(op[0], ID_lt, op[1]);
    }
    else if(statement=="dup")
    {
      assert(op.size()==1 && results.size()==2);
      results[0]=results[1]=op[0];
    }
    else if(statement=="dup_x1")
    {
      assert(op.size()==2 && results.size()==3);
      results[0]=op[1];
      results[1]=op[0];
      results[2]=op[1];
    }
    else if(statement=="dup_x2")
    {
      assert(op.size()==3 && results.size()==4);
      results[0]=op[2];
      results[1]=op[0];
      results[2]=op[1];
      results[3]=op[2];
    }
    // dup2* behaviour depends on the size of the operands on the
    // stack
    else if(statement=="dup2")
    {
      assert(!stack.empty() && results.empty());

      if(get_bytecode_type_width(stack.back().type())==32)
        op=pop(2);
      else
        op=pop(1);

      results.insert(results.end(), op.begin(), op.end());
      results.insert(results.end(), op.begin(), op.end());
    }
    else if(statement=="dup2_x1")
    {
      assert(!stack.empty() && results.empty());

      if(get_bytecode_type_width(stack.back().type())==32)
        op=pop(3);
      else
        op=pop(2);

      results.insert(results.end(), op.begin()+1, op.end());
      results.insert(results.end(), op.begin(), op.end());
    }
    else if(statement=="dup2_x2")
    {
      assert(!stack.empty() && results.empty());

      if(get_bytecode_type_width(stack.back().type())==32)
        op=pop(2);
      else
        op=pop(1);

      assert(!stack.empty());
      exprt::operandst op2;

      if(get_bytecode_type_width(stack.back().type())==32)
        op2=pop(2);
      else
        op2=pop(1);

      results.insert(results.end(), op.begin(), op.end());
      results.insert(results.end(), op2.begin(), op2.end());
      results.insert(results.end(), op.begin(), op.end());
    }
    else if(statement=="dconst")
    {
      assert(op.empty() && results.size()==1);
    }
    else if(statement=="fconst")
    {
      assert(op.empty() && results.size()==1);
    }
    else if(statement=="getfield")
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=java_bytecode_promotion(to_member(op[0], arg0));
    }
    else if(statement=="getstatic")
    {
      assert(op.empty() && results.size()==1);
      symbol_exprt symbol_expr(arg0.type());
      const auto &field_name=arg0.get_string(ID_component_name);
      const bool is_assertions_disabled_field=
        field_name.find("$assertionsDisabled")!=std::string::npos;
      symbol_expr.set_identifier(arg0.get_string(ID_class)+"."+field_name);

      // If external, create a symbol table entry for this static field:
      check_static_field_stub(symbol_expr, field_name);

      if(lazy_methods)
      {
        if(arg0.type().id()==ID_symbol)
        {
          lazy_methods->add_needed_class(
            to_symbol_type(arg0.type()).get_identifier());
        }
        else if(arg0.type().id()==ID_pointer)
        {
          const auto &pointer_type=to_pointer_type(arg0.type());
          if(pointer_type.subtype().id()==ID_symbol)
          {
            lazy_methods->add_needed_class(
              to_symbol_type(pointer_type.subtype()).get_identifier());
          }
        }
        else if(is_assertions_disabled_field)
        {
          lazy_methods->add_needed_class(arg0.get_string(ID_class));
        }
      }
      results[0]=java_bytecode_promotion(symbol_expr);

      codet clinit_call=get_clinit_call(arg0.get_string(ID_class));
      if(clinit_call.get_statement()!=ID_skip)
        c=clinit_call;
      else if(is_assertions_disabled_field)
      {
        // set $assertionDisabled to false
        c=code_assignt(symbol_expr, false_exprt());
      }
    }
    else if(statement=="putfield")
    {
      assert(op.size()==2 && results.empty());
      code_blockt block;
      save_stack_entries(
        "stack_field",
        op[1].type(),
        block,
        bytecode_write_typet::FIELD,
        arg0.get(ID_component_name));
      block.copy_to_operands(code_assignt(to_member(op[0], arg0), op[1]));
      c=block;
    }
    else if(statement=="putstatic")
    {
      assert(op.size()==1 && results.empty());
      symbol_exprt symbol_expr(arg0.type());
      const auto &field_name=arg0.get_string(ID_component_name);
      symbol_expr.set_identifier(arg0.get_string(ID_class)+"."+field_name);

      // If external, create a symbol table entry for this static field:
      check_static_field_stub(symbol_expr, field_name);

      if(lazy_methods && arg0.type().id()==ID_symbol)
      {
        lazy_methods->add_needed_class(
          to_symbol_type(arg0.type()).get_identifier());
      }

      code_blockt block;
      block.add_source_location()=i_it->source_location;

      codet clinit_call=get_clinit_call(arg0.get_string(ID_class));
      if(clinit_call.get_statement()!=ID_skip)
        block.move_to_operands(clinit_call);

      save_stack_entries(
        "stack_static_field",
        symbol_expr.type(),
        block,
        bytecode_write_typet::STATIC_FIELD,
        symbol_expr.get_identifier());
      block.copy_to_operands(code_assignt(symbol_expr, op[0]));
      c=block;
    }
    else if(statement==patternt("?2?")) // i2c etc.
    {
      assert(op.size()==1 && results.size()==1);
      typet type=java_type_from_char(statement[2]);
      results[0]=op[0];
      if(results[0].type()!=type)
        results[0].make_typecast(type);
    }
    else if(statement=="new")
    {
      // use temporary since the stack symbol might get duplicated
      assert(op.empty() && results.size()==1);
      const reference_typet ref_type=java_reference_type(arg0.type());
      exprt java_new_expr=side_effect_exprt(ID_java_new, ref_type);

      if(!i_it->source_location.get_line().empty())
        java_new_expr.add_source_location()=i_it->source_location;

      const exprt tmp=tmp_variable("new", ref_type);
      c=code_assignt(tmp, java_new_expr);
      c.add_source_location()=i_it->source_location;
      codet clinit_call=
        get_clinit_call(to_symbol_type(arg0.type()).get_identifier());
      if(clinit_call.get_statement()!=ID_skip)
      {
        code_blockt ret_block;
        ret_block.move_to_operands(clinit_call);
        ret_block.move_to_operands(c);
        c=std::move(ret_block);
      }
      results[0]=tmp;
    }
    else if(statement=="newarray" ||
            statement=="anewarray")
    {
      // the op is the array size
      assert(op.size()==1 && results.size()==1);

      char element_type;

      if(statement=="newarray")
      {
        irep_idt id=arg0.type().id();

        if(id==ID_bool)
          element_type='z';
        else if(id==ID_char)
          element_type='c';
        else if(id==ID_float)
          element_type='f';
        else if(id==ID_double)
          element_type='d';
        else if(id==ID_byte)
          element_type='b';
        else if(id==ID_short)
          element_type='s';
        else if(id==ID_int)
          element_type='i';
        else if(id==ID_long)
          element_type='j';
        else
          element_type='?';
      }
      else
        element_type='a';

      const reference_typet ref_type=
        java_array_type(element_type);

      side_effect_exprt java_new_array(ID_java_new_array, ref_type);
      java_new_array.copy_to_operands(op[0]);

      if(!i_it->source_location.get_line().empty())
        java_new_array.add_source_location()=i_it->source_location;

      c=code_blockt();

      if(max_array_length!=0)
      {
        constant_exprt size_limit=
          from_integer(max_array_length, java_int_type());
        binary_relation_exprt le_max_size(op[0], ID_le, size_limit);
        code_assumet assume_le_max_size(le_max_size);
        c.move_to_operands(assume_le_max_size);
      }
      const exprt tmp=tmp_variable("newarray", ref_type);
      c.copy_to_operands(code_assignt(tmp, java_new_array));
      results[0]=tmp;
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

      const reference_typet ref_type=
        java_reference_type(arg0.type());

      side_effect_exprt java_new_array(ID_java_new_array, ref_type);
      java_new_array.operands()=op;

      if(!i_it->source_location.get_line().empty())
        java_new_array.add_source_location()=i_it->source_location;

      code_blockt create;

      if(max_array_length!=0)
      {
        constant_exprt size_limit=
          from_integer(max_array_length, java_int_type());
        binary_relation_exprt le_max_size(op[0], ID_le, size_limit);
        code_assumet assume_le_max_size(le_max_size);
        create.move_to_operands(assume_le_max_size);
      }

      const exprt tmp=tmp_variable("newarray", ref_type);
      create.copy_to_operands(code_assignt(tmp, java_new_array));
      c=std::move(create);
      results[0]=tmp;
    }
    else if(statement=="arraylength")
    {
      assert(op.size()==1 && results.size()==1);

      exprt pointer=
        typecast_exprt(op[0], java_array_type(statement[0]));

      dereference_exprt array(pointer, pointer.type().subtype());
      assert(pointer.type().subtype().id()==ID_symbol);
      array.set(ID_java_member_access, true);

      const member_exprt length(array, "length", java_int_type());

      results[0]=length;
    }
    else if(statement=="tableswitch" ||
            statement=="lookupswitch")
    {
      assert(op.size()==1 && results.empty());

      // we turn into switch-case
      code_switcht code_switch;
      code_switch.add_source_location()=i_it->source_location;
      code_switch.value()=op[0];
      code_blockt code_block;
      code_block.add_source_location()=i_it->source_location;

      bool is_label=true;
      for(instructiont::argst::const_iterator
          a_it=i_it->args.begin();
          a_it!=i_it->args.end();
          a_it++, is_label=!is_label)
      {
        if(is_label)
        {
          code_switch_caset code_case;
          code_case.add_source_location()=i_it->source_location;

          mp_integer number;
          bool ret=to_integer(to_constant_expr(*a_it), number);
          DATA_INVARIANT(!ret, "case label expected to be integer");
          code_case.code()=code_gotot(label(integer2string(number)));
          code_case.code().add_source_location()=
            address_map.at(integer2unsigned(number)).source->source_location;

          if(a_it==i_it->args.begin())
            code_case.set_default();
          else
          {
            instructiont::argst::const_iterator prev=a_it;
            prev--;
            code_case.case_op()=*prev;
            if(code_case.case_op().type()!=op[0].type())
              code_case.case_op().make_typecast(op[0].type());
            code_case.case_op().add_source_location()=i_it->source_location;
          }

          code_block.add(code_case);
        }
      }

      code_switch.body()=code_block;
      c=code_switch;
    }
    else if(statement=="pop" || statement=="pop2")
    {
      // these are skips
      c=code_skipt();

      // pop2 removes two single-word items from the stack (e.g. two
      // integers, or an integer and an object reference) or one
      // two-word item (i.e. a double or a long).
      // http://cs.au.dk/~mis/dOvs/jvmspec/ref-pop2.html
      if(statement=="pop2" &&
         get_bytecode_type_width(op[0].type())==32)
        pop(1);
    }
    else if(statement=="instanceof")
    {
      assert(op.size()==1 && results.size()==1);

      results[0]=
        binary_predicate_exprt(op[0], ID_java_instanceof, arg0);
    }
    else if(statement=="monitorenter")
    {
      // becomes a function call
      code_typet type;
      type.return_type()=void_typet();
      type.parameters().resize(1);
      type.parameters()[0].type()=java_reference_type(void_typet());
      code_function_callt call;
      call.function()=symbol_exprt("java::monitorenter", type);
      call.lhs().make_nil();
      call.arguments().push_back(op[0]);
      call.add_source_location()=i_it->source_location;
      c=call;
    }
    else if(statement=="monitorexit")
    {
      // becomes a function call
      code_typet type;
      type.return_type()=void_typet();
      type.parameters().resize(1);
      type.parameters()[0].type()=java_reference_type(void_typet());
      code_function_callt call;
      call.function()=symbol_exprt("java::monitorexit", type);
      call.lhs().make_nil();
      call.arguments().push_back(op[0]);
      call.add_source_location()=i_it->source_location;
      c=call;
    }
    else if(statement=="swap")
    {
      assert(op.size()==2 && results.size()==2);
      results[1]=op[0];
      results[0]=op[1];
    }
    else
    {
      c=codet(statement);
      c.operands()=op;
    }

    // next we do the exception handling
    std::vector<irep_idt> exception_ids;
    std::vector<irep_idt> handler_labels;

    // for each try-catch add a CATCH-PUSH instruction
    // each CATCH-PUSH records a list of all the handler labels
    // together with a list of all the exception ids

    // be aware of different try-catch blocks with the same starting pc
    std::size_t pos=0;
    std::size_t end_pc=0;
    while(pos<method.exception_table.size())
    {
      // check if this is the beginning of a try block
      for(; pos<method.exception_table.size(); ++pos)
      {
        // unexplored try-catch?
        if(cur_pc==method.exception_table[pos].start_pc && end_pc==0)
        {
          end_pc=method.exception_table[pos].end_pc;
        }

        // currently explored try-catch?
        if(cur_pc==method.exception_table[pos].start_pc &&
           method.exception_table[pos].end_pc==end_pc)
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
          exception_ids.size()==handler_labels.size(),
          "Exception tags and handler labels should be 1-to-1");
        code_push_catcht::exception_listt &exception_list=
          catch_push.exception_list();
        for(size_t i=0; i<exception_ids.size(); ++i)
        {
          exception_list.push_back(
            code_push_catcht::exception_list_entryt(
              exception_ids[i],
              handler_labels[i]));
        }

        code_blockt try_block;
        try_block.move_to_operands(catch_push);
        try_block.move_to_operands(c);
        c=try_block;
      }
      else
      {
        // advance
        ++pos;
      }

      // reset
      end_pc=0;
      exception_ids.clear();
      handler_labels.clear();
    }

    // next add the CATCH-POP instructions
    size_t start_pc=0;
    // as the first try block may have start_pc 0, we
    // must track it separately
    bool first_handler=false;
    // check if this is the end of a try block
    for(const auto &exception_row : method.exception_table)
    {
      // add the CATCH-POP before the end of the try block
      if(cur_pc<exception_row.end_pc &&
         !working_set.empty() &&
         *working_set.begin()==exception_row.end_pc)
      {
        // have we already added a CATCH-POP for the current try-catch?
        // (each row corresponds to a handler)
        if(exception_row.start_pc!=start_pc || !first_handler)
        {
          if(!first_handler)
            first_handler=true;
          // remember the beginning of the try-catch so that we don't add
          // another CATCH-POP for the same try-catch
          start_pc=exception_row.start_pc;
          // add CATCH_POP instruction
          code_pop_catcht catch_pop;
          code_blockt end_try_block;
          end_try_block.move_to_operands(c);
          end_try_block.move_to_operands(catch_pop);
          c=end_try_block;
        }
      }
    }

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

    a_it->second.done=true;
    for(const unsigned address : a_it->second.successors)
    {
      address_mapt::iterator a_it2=address_map.find(address);
      assert(a_it2!=address_map.end());

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
          assert(a_it2->second.stack.size()==stack.size());
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
  unsigned previous_address=0;
  for(const auto &address_pair : address_map)
  {
    const unsigned address=address_pair.first;
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
      v.start_pc+v.length,
      std::numeric_limits<unsigned>::max(),
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
    auto &block=get_block_for_pcrange(
      root,
      root_block,
      v.start_pc,
      v.start_pc+v.length,
      std::numeric_limits<unsigned>::max());
    code_declt d(v.symbol_expr);
    block.operands().insert(block.operands().begin(), d);
  }

  for(auto &block : root_block.operands())
    code.move_to_operands(block);

  return code;
}

void java_bytecode_convert_method(
  const symbolt &class_symbol,
  const java_bytecode_parse_treet::methodt &method,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  safe_pointer<ci_lazy_methods_neededt> lazy_methods,
  java_string_library_preprocesst &string_preprocess)
{
  static const std::unordered_set<std::string> methods_to_ignore
  {
    "nondetBoolean",
    "nondetByte",
    "nondetChar",
    "nondetShort",
    "nondetInt",
    "nondetLong",
    "nondetFloat",
    "nondetDouble",
    "nondetWithNull",
    "nondetWithoutNull",
    "notModelled",
  };

  if(std::regex_match(
       id2string(class_symbol.name),
       std::regex(".*org\\.cprover\\.CProver.*")) &&
     methods_to_ignore.find(id2string(method.name))!=methods_to_ignore.end())
  {
    // Ignore these methods, rely on default stubbing behaviour.
    return;
  }

  java_bytecode_convert_methodt java_bytecode_convert_method(
    symbol_table,
    message_handler,
    max_array_length,
    lazy_methods,
    string_preprocess);

  java_bytecode_convert_method(class_symbol, method);
}

/// Returns true iff method \p methodid from class \p classname is
/// a method inherited from a class (and not an interface!) from which
/// \p classname inherits, either directly or indirectly.
bool java_bytecode_convert_methodt::is_method_inherited(
  const irep_idt &classname, const irep_idt &methodid) const
{
  resolve_concrete_function_callt call_resolver(symbol_table);
  const resolve_concrete_function_callt ::concrete_function_callt &
    resolved_call=call_resolver(classname, methodid);

  // resolved_call is a pair (class-name, method-name) found by walking the
  // chain of class inheritance (not interfaces!) and stopping on the first
  // class that contains a method of equal name and type to `methodid`

  if(resolved_call.is_valid())
  {
    const symbolt &function_symbol=
      *symbol_table.lookup(resolved_call.get_virtual_method_name());

    INVARIANT(function_symbol.type.id()==ID_code, "Function must be code");

    const auto &access=function_symbol.type.get(ID_access);
    if(access==ID_public || access==ID_protected)
    {
      // since the method is public, it is a public method of `classname`, it is
      // inherited
      return true;
    }

    // methods with the default access modifier are only
    // accessible within the same package.
    if(access==ID_default)
    {
      const std::string &class_package=
        java_class_to_package(id2string(classname));
      const std::string &method_package=
        java_class_to_package(id2string(resolved_call.get_class_identifier()));
      return method_package==class_package;
    }

    if(access==ID_private)
    {
      // We return false because the method found by the call_resolver above
      // proves that `methodid` cannot be inherited (assuming that the original
      // Java code compiles). This is because, as we walk the inheritance chain
      // for `classname` from Object to `classname`, a method can only become
      // "more accessible". So, if the last occurrence is private, all others
      // before must be private as well, and none is inherited in `classname`.
      return false;
    }

    INVARIANT(false, "Unexpected access modifier.");
  }

  return false;
}

/// create temporary variables if a write instruction can have undesired side-
/// effects
void java_bytecode_convert_methodt::save_stack_entries(
  const std::string &tmp_var_prefix,
  const typet &tmp_var_type,
  code_blockt &block,
  const bytecode_write_typet write_type,
  const irep_idt &identifier)
{
  for(auto &stack_entry : stack)
  {
    // remove typecasts if existing
    while(stack_entry.id()==ID_typecast)
      stack_entry=to_typecast_expr(stack_entry).op();

    // variables or static fields and symbol -> save symbols with same id
    if((write_type==bytecode_write_typet::VARIABLE ||
        write_type==bytecode_write_typet::STATIC_FIELD) &&
       stack_entry.id()==ID_symbol)
    {
      const symbol_exprt &var=to_symbol_expr(stack_entry);
      if(var.get_identifier()==identifier)
        create_stack_tmp_var(tmp_var_prefix, tmp_var_type, block, stack_entry);
    }

    // array reference and dereference -> save all references on the stack
    else if(write_type==bytecode_write_typet::ARRAY_REF &&
            stack_entry.id()==ID_dereference)
      create_stack_tmp_var(tmp_var_prefix, tmp_var_type, block, stack_entry);

    // field and member access -> compare component name
    else if(write_type==bytecode_write_typet::FIELD &&
            stack_entry.id()==ID_member)
    {
      const irep_idt &entry_id=
        to_member_expr(stack_entry).get_component_name();
      if(entry_id==identifier)
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

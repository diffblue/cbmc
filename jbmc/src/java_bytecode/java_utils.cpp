/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_utils.h"

#include "java_root_class.h"
#include "java_string_library_preprocess.h"

#include <util/fresh_symbol.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/prefix.h>
#include <util/std_types.h>
#include <util/string_utils.h>

#include <set>
#include <unordered_set>

bool is_java_string_type(const struct_typet &struct_type)
{
  return java_string_library_preprocesst::implements_java_char_sequence(
           struct_type) &&
         struct_type.has_component("length") &&
         struct_type.has_component("data");
}

const java_boxed_type_infot *
get_boxed_type_info_by_name(const irep_idt &type_name)
{
  static std::unordered_map<irep_idt, java_boxed_type_infot> type_info_by_name =
    {
      {"java::java.lang.Boolean",
       {"java::java.lang.Boolean.booleanValue:()Z", java_boolean_type()}},
      {"java::java.lang.Byte",
       {"java::java.lang.Byte.byteValue:()B", java_byte_type()}},
      {"java::java.lang.Character",
       {"java::java.lang.Character.charValue:()C", java_char_type()}},
      {"java::java.lang.Double",
       {"java::java.lang.Double.doubleValue:()D", java_double_type()}},
      {"java::java.lang.Float",
       {"java::java.lang.Float.floatValue:()F", java_float_type()}},
      {"java::java.lang.Integer",
       {"java::java.lang.Integer.intValue:()I", java_int_type()}},
      {"java::java.lang.Long",
       {"java::java.lang.Long.longValue:()J", java_long_type()}},
      {"java::java.lang.Short",
       {"java::java.lang.Short.shortValue:()S", java_short_type()}},
    };

  auto found = type_info_by_name.find(type_name);
  return found == type_info_by_name.end() ? nullptr : &found->second;
}

const java_primitive_type_infot *
get_java_primitive_type_info(const typet &maybe_primitive_type)
{
  static std::unordered_map<typet, java_primitive_type_infot, irep_hash>
    type_info_by_primitive_type = {
      {java_boolean_type(),
       {"java::java.lang.Boolean",
        "java::java.lang.Boolean.valueOf:(Z)Ljava/lang/Boolean;",
        "java::java.lang.Boolean.booleanValue:()Z"}},
      {java_byte_type(),
       {"java::java.lang.Byte",
        "java::java.lang.Byte.valueOf:(B)Ljava/lang/Byte;",
        "java::java.lang.Number.byteValue:()B"}},
      {java_char_type(),
       {"java::java.lang.Character",
        "java::java.lang.Character.valueOf:(C)"
        "Ljava/lang/Character;",
        "java::java.lang.Character.charValue:()C"}},
      {java_double_type(),
       {"java::java.lang.Double",
        "java::java.lang.Double.valueOf:(D)"
        "Ljava/lang/Double;",
        "java::java.lang.Number.doubleValue:()D"}},
      {java_float_type(),
       {"java::java.lang.Float",
        "java::java.lang.Float.valueOf:(F)"
        "Ljava/lang/Float;",
        "java::java.lang.Number.floatValue:()F"}},
      {java_int_type(),
       {"java::java.lang.Integer",
        "java::java.lang.Integer.valueOf:(I)"
        "Ljava/lang/Integer;",
        "java::java.lang.Number.intValue:()I"}},
      {java_long_type(),
       {"java::java.lang.Long",
        "java::java.lang.Long.valueOf:(J)Ljava/lang/Long;",
        "java::java.lang.Number.longValue:()J"}},
      {java_short_type(),
       {"java::java.lang.Short",
        "java::java.lang.Short.valueOf:(S)"
        "Ljava/lang/Short;",
        "java::java.lang.Number.shortValue:()S"}}};

  auto found = type_info_by_primitive_type.find(maybe_primitive_type);
  return found == type_info_by_primitive_type.end() ? nullptr : &found->second;
}

bool is_primitive_wrapper_type_id(const irep_idt &id)
{
  return get_boxed_type_info_by_name(id) != nullptr;
}

bool is_primitive_wrapper_type_name(const std::string &type_name)
{
  static const std::unordered_set<std::string> primitive_wrapper_type_names = {
    "java.lang.Boolean",
    "java.lang.Byte",
    "java.lang.Character",
    "java.lang.Double",
    "java.lang.Float",
    "java.lang.Integer",
    "java.lang.Long",
    "java.lang.Short"};
  return primitive_wrapper_type_names.count(type_name) > 0;
}

unsigned java_local_variable_slots(const typet &t)
{

  // Even on a 64-bit platform, Java pointers occupy one slot:
  if(t.id()==ID_pointer)
    return 1;

  const std::size_t bitwidth = to_bitvector_type(t).get_width();
  INVARIANT(
    bitwidth==8 ||
    bitwidth==16 ||
    bitwidth==32 ||
    bitwidth==64,
    "all types constructed in java_types.cpp encode JVM types "
    "with these bit widths");

  return bitwidth == 64 ? 2u : 1u;
}

unsigned java_method_parameter_slots(const java_method_typet &t)
{
  unsigned slots=0;

  for(const auto &p : t.parameters())
    slots+=java_local_variable_slots(p.type());

  return slots;
}

const std::string java_class_to_package(const std::string &canonical_classname)
{
  return trim_from_last_delimiter(canonical_classname, '.');
}

void generate_class_stub(
  const irep_idt &class_name,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  const struct_union_typet::componentst &componentst)
{
  java_class_typet class_type;

  class_type.set_tag(class_name);
  class_type.set_is_stub(true);

  // produce class symbol
  symbolt new_symbol;
  new_symbol.base_name=class_name;
  new_symbol.pretty_name=class_name;
  new_symbol.name="java::"+id2string(class_name);
  class_type.set_name(new_symbol.name);
  new_symbol.type=class_type;
  new_symbol.mode=ID_java;
  new_symbol.is_type=true;

  std::pair<symbolt &, bool> res=symbol_table.insert(std::move(new_symbol));

  if(!res.second)
  {
    messaget message(message_handler);
    message.warning() <<
      "stub class symbol " <<
      new_symbol.name <<
      " already exists" << messaget::eom;
  }
  else
  {
    // create the class identifier etc
    java_root_class(res.first);
    java_add_components_to_class(res.first, componentst);
  }
}

void merge_source_location_rec(
  exprt &expr,
  const source_locationt &source_location)
{
  expr.add_source_location().merge(source_location);
  for(exprt &op : expr.operands())
    merge_source_location_rec(op, source_location);
}

bool is_java_string_literal_id(const irep_idt &id)
{
  return has_prefix(id2string(id), JAVA_STRING_LITERAL_PREFIX);
}

irep_idt resolve_friendly_method_name(
  const std::string &friendly_name,
  const symbol_table_baset &symbol_table,
  std::string &error)
{
  std::string qualified_name="java::"+friendly_name;
  if(friendly_name.rfind(':')==std::string::npos)
  {
    std::string prefix=qualified_name+':';
    std::set<irep_idt> matches;

    for(const auto &s : symbol_table.symbols)
      if(has_prefix(id2string(s.first), prefix) &&
         s.second.type.id()==ID_code)
        matches.insert(s.first);

    if(matches.empty())
    {
      error="'"+friendly_name+"' not found";
      return irep_idt();
    }
    else if(matches.size()>1)
    {
      std::ostringstream message;
      message << "'"+friendly_name+"' is ambiguous between:";

      // Trim java:: prefix so we can recommend an appropriate input:
      for(const auto &s : matches)
        message << "\n  " << id2string(s).substr(6);

      error=message.str();
      return irep_idt();
    }
    else
    {
      return *matches.begin();
    }
  }
  else
  {
    auto findit=symbol_table.symbols.find(qualified_name);
    if(findit==symbol_table.symbols.end())
    {
      error="'"+friendly_name+"' not found";
      return irep_idt();
    }
    else if(findit->second.type.id()!=ID_code)
    {
      error="'"+friendly_name+"' not a function";
      return irep_idt();
    }
    else
    {
      return findit->first;
    }
  }
}

pointer_typet pointer_to_replacement_type(
  const pointer_typet &given_pointer_type,
  const java_class_typet &replacement_class_type)
{
  if(can_cast_type<struct_tag_typet>(given_pointer_type.base_type()))
  {
    struct_tag_typet struct_tag_subtype{replacement_class_type.get_name()};
    return pointer_type(struct_tag_subtype);
  }
  return pointer_type(replacement_class_type);
}

dereference_exprt checked_dereference(const exprt &expr)
{
  dereference_exprt result(expr);
  // tag it so it's easy to identify during instrumentation
  result.set(ID_java_member_access, true);
  return result;
}

/// Finds the corresponding closing delimiter to the given opening delimiter. It
/// is assumed that \p open_pos points to the opening delimiter \p open_char in
/// the \p src string. The depth of nesting is counted to identify the correct
/// closing delimiter.
///
/// A typical use case is for example Java generic types, e.g., List<List<T>>
///
/// \param src: the source string to scan
/// \param open_pos: the initial position of the opening delimiter from where to
///   start the search
/// \param open_char: the opening delimiter
/// \param close_char: the closing delimiter
/// \return the index of the matching corresponding closing delimiter in \p src
size_t find_closing_delimiter(
  const std::string &src,
  size_t open_pos,
  char open_char,
  char close_char)
{
  // having the same opening and closing delimiter does not allow for hierarchic
  // structuring
  PRECONDITION(open_char!=close_char);
  PRECONDITION(src[open_pos]==open_char);
  size_t c_pos=open_pos+1;
  const size_t end_pos=src.size()-1;
  size_t depth=0;

  while(c_pos<=end_pos)
  {
    if(src[c_pos] == open_char)
      depth++;
    else if(src[c_pos] == close_char)
    {
      if(depth==0)
        return c_pos;
      depth--;
    }
    c_pos++;
    // limit depth to sensible values
    INVARIANT(
      depth<=(src.size()-open_pos),
      "No closing \'"+std::to_string(close_char)+
      "\' found in signature to parse.");
  }
  // did not find corresponding closing '>'
  return std::string::npos;
}

/// Add the components in components_to_add to the class denoted by
/// class symbol.
/// \param class_symbol: The symbol representing the class we want to modify.
/// \param components_to_add: The vector with the components we want to add.
void java_add_components_to_class(
  symbolt &class_symbol,
  const struct_union_typet::componentst &components_to_add)
{
  PRECONDITION(class_symbol.is_type);
  PRECONDITION(class_symbol.type.id()==ID_struct);
  struct_typet &struct_type=to_struct_type(class_symbol.type);
  struct_typet::componentst &components=struct_type.components();
  components.insert(
    components.end(), components_to_add.begin(), components_to_add.end());
}

/// Declare a function with the given name and type.
/// \param function_name: a name
/// \param type: a type
/// \param symbol_table: symbol table
/// \return newly created symbol
static auxiliary_symbolt declare_function(
  const irep_idt &function_name,
  const mathematical_function_typet &type,
  symbol_table_baset &symbol_table)
{
  auxiliary_symbolt func_symbol;
  func_symbol.base_name=function_name;
  func_symbol.pretty_name=function_name;
  func_symbol.is_static_lifetime=false;
  func_symbol.is_state_var = false;
  func_symbol.mode=ID_java;
  func_symbol.name=function_name;
  func_symbol.type=type;
  symbol_table.add(func_symbol);

  return func_symbol;
}

/// Create a (mathematical) function application expression.
/// The application has the type of the codomain (range) of the function.
/// \param function_name: the name of the function
/// \param arguments: a list of arguments (an element of the domain)
/// \param range: return type (codomain) of the function
/// \param symbol_table: a symbol table
/// \return a function application expression representing:
///   `function_name(arguments)`
exprt make_function_application(
  const irep_idt &function_name,
  const exprt::operandst &arguments,
  const typet &range,
  symbol_table_baset &symbol_table)
{
  std::vector<typet> argument_types;
  for(const auto &arg : arguments)
    argument_types.push_back(arg.type());

  // Declaring the function
  const auto symbol = declare_function(
    function_name,
    mathematical_function_typet(std::move(argument_types), range),
    symbol_table);

  // Function application
  return function_application_exprt{symbol.symbol_expr(), arguments};
}

/// Strip java:: prefix from given identifier
/// \param to_strip: identifier from which the prefix is stripped
/// \return the identifier without without java:: prefix
irep_idt strip_java_namespace_prefix(const irep_idt &to_strip)
{
  const std::string to_strip_str=id2string(to_strip);
  const std::string prefix="java::";

  PRECONDITION(has_prefix(to_strip_str, prefix));
  return to_strip_str.substr(prefix.size(), std::string::npos);
}

/// Strip the package name from a java type, for the type to be
/// pretty printed (java::java.lang.Integer -> Integer).
/// \param fqn_java_type: The java type we want to pretty print.
/// \return The pretty printed type if there was a match of the
///   qualifiers, or the type as it was passed otherwise.
std::string pretty_print_java_type(const std::string &fqn_java_type)
{
  std::string result(fqn_java_type);
  const std::string java_cbmc_string("java::");
  // Remove the CBMC internal java identifier
  if(has_prefix(fqn_java_type, java_cbmc_string))
    result = fqn_java_type.substr(java_cbmc_string.length());
  // If the class is in package java.lang strip
  // package name due to default import
  const std::string java_lang_string("java.lang.");
  if(has_prefix(result, java_lang_string))
    result = result.substr(java_lang_string.length());
  return result;
}

/// Finds an inherited component (method or field), taking component visibility
/// into account.
/// \param component_class_id: class to start searching from. For example, if
///   trying to resolve a reference to A.b, component_class_id is "A".
/// \param component_name: component basename to search for. If searching for
///   A.b, this is "b".
/// \param symbol_table: global symbol table.
/// \param include_interfaces: if true, search for the given component in all
///   ancestors including interfaces, rather than just parents.
/// \return the concrete component referred to if any is found, or an invalid
///   resolve_inherited_componentt::inherited_componentt otherwise.
optionalt<resolve_inherited_componentt::inherited_componentt>
get_inherited_component(
  const irep_idt &component_class_id,
  const irep_idt &component_name,
  const symbol_tablet &symbol_table,
  bool include_interfaces)
{
  resolve_inherited_componentt component_resolver{symbol_table};
  const auto resolved_component =
    component_resolver(component_class_id, component_name, include_interfaces);

  // resolved_component is a pair (class-name, component-name) found by walking
  // the chain of class inheritance (not interfaces!) and stopping on the first
  // class that contains a component of equal name and type to `component_name`

  if(resolved_component)
  {
    // Directly defined on the class referred to?
    if(component_class_id == resolved_component->get_class_identifier())
      return *resolved_component;

    // No, may be inherited from some parent class; check it is visible:
    const symbolt &component_symbol = symbol_table.lookup_ref(
      resolved_component->get_full_component_identifier());

    irep_idt access = component_symbol.type.get(ID_access);
    if(access.empty())
      access = component_symbol.type.get(ID_C_access);

    if(access==ID_public || access==ID_protected)
    {
      // since the component is public, it is inherited
      return *resolved_component;
    }

    // components with the default access modifier are only
    // accessible within the same package.
    if(access==ID_default)
    {
      const std::string &class_package=
        java_class_to_package(id2string(component_class_id));
      const std::string &component_package = java_class_to_package(
        id2string(resolved_component->get_class_identifier()));
      if(component_package == class_package)
        return *resolved_component;
      else
        return {};
    }

    if(access==ID_private)
    {
      // We return not-found because the component found by the
      // component_resolver above proves that `component_name` cannot be
      // inherited (assuming that the original Java code compiles). This is
      // because, as we walk the inheritance chain for `classname` from Object
      // to `classname`, a component can only become "more accessible". So, if
      // the last occurrence is private, all others before must be private as
      // well, and none is inherited in `classname`.
      return {};
    }

    UNREACHABLE; // Unexpected access modifier
  }
  else
  {
    return {};
  }
}

/// Check if a symbol is a well-known non-null global
/// \param symbolid: symbol id to check
/// \return true if this static field is known never to be null
bool is_non_null_library_global(const irep_idt &symbolid)
{
  static const irep_idt in = "java::java.lang.System.in";
  static const irep_idt out = "java::java.lang.System.out";
  static const irep_idt err = "java::java.lang.System.err";
  return symbolid == in || symbolid == out || symbolid == err;
}

/// Methods belonging to the class org.cprover.CProver that should be ignored
/// (not converted), leaving the driver program to stub them if it wishes.
const std::unordered_set<std::string> cprover_methods_to_ignore{
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
  "atomicBegin",
  "atomicEnd",
  "startThread",
  "endThread",
  "getCurrentThreadId",
  "getMonitorCount"};

/// \param type: type of new symbol
/// \param basename_prefix: new symbol will be named
///   function_name::basename_prefix$num
/// \param source_location: new symbol source loc
/// \param function_name: name of the function in which the symbol is defined
/// \param symbol_table: table to add the new symbol to
/// \return fresh-named symbol with the requested name pattern
symbolt &fresh_java_symbol(
  const typet &type,
  const std::string &basename_prefix,
  const source_locationt &source_location,
  const irep_idt &function_name,
  symbol_table_baset &symbol_table)
{
  PRECONDITION(!function_name.empty());
  const std::string name_prefix = id2string(function_name);
  return get_fresh_aux_symbol(
    type, name_prefix, basename_prefix, source_location, ID_java, symbol_table);
}

optionalt<irep_idt> declaring_class(const symbolt &symbol)
{
  const irep_idt &class_id = symbol.type.get(ID_C_class);
  return class_id.empty() ? optionalt<irep_idt>{} : class_id;
}

void set_declaring_class(symbolt &symbol, const irep_idt &declaring_class)
{
  symbol.type.set(ID_C_class, declaring_class);
}

NODISCARD optionalt<std::string>
class_name_from_method_name(const std::string &method_name)
{
  const auto signature_index = method_name.rfind(":");
  const auto method_index = method_name.rfind(".", signature_index);
  if(method_index == std::string::npos)
    return {};
  return method_name.substr(0, method_index);
}

/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Language Conversion

#include "java_bytecode_convert_class.h"

#ifdef DEBUG
#include <iostream>
#endif

#include "java_root_class.h"
#include "java_types.h"
#include "java_bytecode_convert_method.h"
#include "java_bytecode_language.h"
#include "java_utils.h"

#include <util/c_types.h>
#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include <linking/zero_initializer.h>
#include <util/suffix.h>

class java_bytecode_convert_classt:public messaget
{
public:
  java_bytecode_convert_classt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    size_t _max_array_length,
    method_bytecodet &method_bytecode,
    lazy_methods_modet _lazy_methods_mode,
    java_string_library_preprocesst &_string_preprocess)
    : messaget(_message_handler),
      symbol_table(_symbol_table),
      max_array_length(_max_array_length),
      method_bytecode(method_bytecode),
      lazy_methods_mode(_lazy_methods_mode),
      string_preprocess(_string_preprocess)
  {
  }

  void operator()(const java_bytecode_parse_treet &parse_tree)
  {
    // add array types to the symbol table
    add_array_types(symbol_table);

    bool loading_success=parse_tree.loading_successful;
    if(loading_success)
      convert(parse_tree.parsed_class);

    if(string_preprocess.is_known_string_type(parse_tree.parsed_class.name))
      string_preprocess.add_string_type(
        parse_tree.parsed_class.name, symbol_table);
    else if(!loading_success)
      generate_class_stub(
        parse_tree.parsed_class.name,
        symbol_table,
        get_message_handler(),
        struct_union_typet::componentst{});
  }

  typedef java_bytecode_parse_treet::classt classt;
  typedef java_bytecode_parse_treet::fieldt fieldt;

protected:
  symbol_tablet &symbol_table;
  const size_t max_array_length;
  method_bytecodet &method_bytecode;
  lazy_methods_modet lazy_methods_mode;
  java_string_library_preprocesst &string_preprocess;

  // conversion
  void convert(const classt &c);
  void convert(symbolt &class_symbol, const fieldt &f);

  // see definition below for more info
  static void add_array_types(symbol_tablet &symbol_table);
};

/// Auxiliary function to extract the generic superclass reference from the
/// class signature. If the signature is empty or the superclass is not generic
/// it returns empty.
/// Example:
/// - class: A<T> extends B<T, Integer> implements C, D<T>
/// - signature: <T:Ljava/lang/Object;>B<TT;Ljava/lang/Integer;>;LC;LD<TT;>;
/// - returned superclass reference: B<TT;Ljava/lang/Integer;>;
/// \param signature Signature of the class
/// \return Reference of the generic superclass, or empty if the superclass
/// is not generic
static optionalt<std::string>
extract_generic_superclass_reference(const optionalt<std::string> &signature)
{
  if(signature.has_value())
  {
    // skip the (potential) list of generic parameters at the beginning of the
    // signature
    const size_t start =
      signature.value().front() == '<'
        ? find_closing_delimiter(signature.value(), 0, '<', '>') + 1
        : 0;

    // extract the superclass reference
    const size_t end =
      find_closing_semi_colon_for_reference_type(signature.value(), start);
    const std::string superclass_ref =
      signature.value().substr(start, (end - start) + 1);

    // if the superclass is generic then the reference is of form
    // Lsuperclass-name<generic-types;>;
    if(has_suffix(superclass_ref, ">;"))
      return superclass_ref;
  }
  return {};
}

/// Auxiliary function to extract the generic interface reference of an
/// interface with the specified name from the class signature. If the
/// signature is empty or the interface is not generic it returns empty.
/// Example:
/// - class: A<T> extends B<T, Integer> implements C, D<T>
/// - signature: <T:Ljava/lang/Object;>B<TT;Ljava/lang/Integer;>;LC;LD<TT;>;
/// - returned interface reference for C: LC;
/// - returned interface reference for D: LD<TT;>;
/// \param signature Signature of the class
/// \param interface_name The interface name
/// \return Reference of the generic interface, or empty if the interface
/// is not generic
static optionalt<std::string> extract_generic_interface_reference(
  const optionalt<std::string> &signature,
  const std::string &interface_name)
{
  if(signature.has_value())
  {
    // skip the (potential) list of generic parameters at the beginning of the
    // signature
    size_t start =
      signature.value().front() == '<'
        ? find_closing_delimiter(signature.value(), 0, '<', '>') + 1
        : 0;

    // skip the superclass reference (if there is at least one interface
    // reference in the signature, then there is a superclass reference)
    start =
      find_closing_semi_colon_for_reference_type(signature.value(), start) + 1;

    start = signature.value().find("L" + interface_name + "<", start);
    if(start != std::string::npos)
    {
      const size_t &end =
        find_closing_semi_colon_for_reference_type(signature.value(), start);
      return signature.value().substr(start, (end - start) + 1);
    }
  }
  return {};
}

void java_bytecode_convert_classt::convert(const classt &c)
{
  std::string qualified_classname="java::"+id2string(c.name);
  if(symbol_table.has_symbol(qualified_classname))
  {
    debug() << "Skip class " << c.name << " (already loaded)" << eom;
    return;
  }

  java_class_typet class_type;
  if(c.signature.has_value() && c.signature.value()[0]=='<')
  {
    java_generic_class_typet generic_class_type;
#ifdef DEBUG
    std::cout << "INFO: found generic class signature "
              << c.signature.value()
              << " in parsed class "
              << c.name << "\n";
#endif
    try
    {
      const std::vector<typet> &generic_types=java_generic_type_from_string(
        id2string(c.name),
        c.signature.value());
      for(const typet &t : generic_types)
      {
        generic_class_type.generic_types()
          .push_back(to_java_generic_parameter(t));
      }
      class_type=generic_class_type;
    }
    catch(unsupported_java_class_signature_exceptiont)
    {
      warning() << "we currently don't support parsing for example double "
        "bounded, recursive and wild card generics" << eom;
    }
  }

  class_type.set_tag(c.name);
  class_type.set(ID_base_name, c.name);
  class_type.set(ID_abstract, c.is_abstract);
  if(c.is_enum)
  {
    class_type.set(
      ID_java_enum_static_unwind,
      std::to_string(c.enum_elements+1));
    class_type.set(ID_enumeration, true);
  }

  if(c.is_public)
    class_type.set_access(ID_public);
  else if(c.is_protected)
    class_type.set_access(ID_protected);
  else if(c.is_private)
    class_type.set_access(ID_private);
  else
    class_type.set_access(ID_default);

  if(!c.extends.empty())
  {
    const symbol_typet base("java::" + id2string(c.extends));

    // if the superclass is generic then the class has the superclass reference
    // including the generic info in its signature
    // e.g., signature for class 'A<T>' that extends
    // 'Generic<Integer>' is '<T:Ljava/lang/Object;>LGeneric<LInteger;>;'
    const optionalt<std::string> &superclass_ref =
      extract_generic_superclass_reference(c.signature);
    if(superclass_ref.has_value())
    {
      const java_generic_symbol_typet generic_base(
        base, superclass_ref.value(), qualified_classname);
      class_type.add_base(generic_base);
    }
    else
    {
      class_type.add_base(base);
    }
    class_typet::componentt base_class_field;
    base_class_field.type() = class_type.bases().at(0).type();
    base_class_field.set_name("@"+id2string(c.extends));
    base_class_field.set_base_name("@"+id2string(c.extends));
    base_class_field.set_pretty_name("@"+id2string(c.extends));
    class_type.components().push_back(base_class_field);
  }

  // interfaces are recorded as bases
  for(const auto &interface : c.implements)
  {
    const symbol_typet base("java::" + id2string(interface));

    // if the interface is generic then the class has the interface reference
    // including the generic info in its signature
    // e.g., signature for class 'A implements GenericInterface<Integer>' is
    // 'Ljava/lang/Object;LGenericInterface<LInteger;>;'
    const optionalt<std::string> interface_ref =
      extract_generic_interface_reference(c.signature, id2string(interface));
    if(interface_ref.has_value())
    {
      const java_generic_symbol_typet generic_base(
        base, interface_ref.value(), qualified_classname);
      class_type.add_base(generic_base);
    }
    else
    {
      class_type.add_base(base);
    }
  }

  // produce class symbol
  symbolt new_symbol;
  new_symbol.base_name=c.name;
  new_symbol.pretty_name=c.name;
  new_symbol.name=qualified_classname;
  class_type.set(ID_name, new_symbol.name);
  new_symbol.type=class_type;
  new_symbol.mode=ID_java;
  new_symbol.is_type=true;

  symbolt *class_symbol;

  // add before we do members
  debug() << "Adding symbol: class '" << c.name << "'" << eom;
  if(symbol_table.move(new_symbol, class_symbol))
  {
    error() << "failed to add class symbol " << new_symbol.name << eom;
    throw 0;
  }

  // now do fields
  for(const auto &field : c.fields)
  {
    debug() << "Adding symbol:  field '" << field.name << "'" << eom;
    convert(*class_symbol, field);
  }

  // now do methods
  for(const auto &method : c.methods)
  {
    const irep_idt method_identifier=
      id2string(qualified_classname)+
      "."+id2string(method.name)+
      ":"+method.descriptor;
    // Always run the lazy pre-stage, as it symbol-table
    // registers the function.
    debug() << "Adding symbol:  method '" << method_identifier << "'" << eom;
    java_bytecode_convert_method_lazy(
      *class_symbol,
      method_identifier,
      method,
      symbol_table,
      get_message_handler());
    method_bytecode.add(qualified_classname, method_identifier, method);
  }

  // is this a root class?
  if(c.extends.empty())
    java_root_class(*class_symbol);
}

void java_bytecode_convert_classt::convert(
  symbolt &class_symbol,
  const fieldt &f)
{
  typet field_type;
  if(f.signature.has_value())
  {
    field_type=java_type_from_string_with_exception(
      f.descriptor,
      f.signature,
      id2string(class_symbol.name));

    /// this is for a free type variable, e.g., a field of the form `T f;`
    if(is_java_generic_parameter(field_type))
    {
#ifdef DEBUG
      std::cout << "fieldtype: generic "
                << to_java_generic_parameter(field_type).type_variable()
                     .get_identifier()
                << " name " << f.name << "\n";
#endif
    }

    /// this is for a field that holds a generic type, either with instantiated
    /// or with free type variables, e.g., `List<T> l;` or `List<Integer> l;`
    else if(is_java_generic_type(field_type))
    {
      java_generic_typet &with_gen_type=
        to_java_generic_type(field_type);
#ifdef DEBUG
      std::cout << "fieldtype: generic container type "
                << std::to_string(with_gen_type.generic_type_arguments().size())
                << " type " << with_gen_type.id()
                << " name " << f.name
                << " subtype id " << with_gen_type.subtype().id() << "\n";
#endif
      field_type=with_gen_type;
    }
  }
  else
    field_type=java_type_from_string(f.descriptor);

  // is this a static field?
  if(f.is_static)
  {
    // Create the symbol; we won't add to the struct type.
    symbolt new_symbol;

    new_symbol.is_static_lifetime=true;
    new_symbol.is_lvalue=true;
    new_symbol.is_state_var=true;
    new_symbol.name=id2string(class_symbol.name)+"."+id2string(f.name);
    new_symbol.base_name=f.name;
    new_symbol.type=field_type;
    new_symbol.pretty_name=id2string(class_symbol.pretty_name)+
      "."+id2string(f.name);
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;
    const namespacet ns(symbol_table);
    new_symbol.value=
      zero_initializer(
        field_type,
        class_symbol.location,
        ns,
        get_message_handler());

    // Do we have the static field symbol already?
    const auto s_it=symbol_table.symbols.find(new_symbol.name);
    if(s_it!=symbol_table.symbols.end())
      symbol_table.erase(s_it); // erase, we stubbed it

    if(symbol_table.add(new_symbol))
      assert(false && "failed to add static field symbol");
  }
  else
  {
    class_typet &class_type=to_class_type(class_symbol.type);

    class_type.components().push_back(class_typet::componentt());
    class_typet::componentt &component=class_type.components().back();

    component.set_name(f.name);
    component.set_base_name(f.name);
    component.set_pretty_name(f.name);
    component.type()=field_type;

    if(f.is_private)
      component.set_access(ID_private);
    else if(f.is_protected)
      component.set_access(ID_protected);
    else if(f.is_public)
      component.set_access(ID_public);
    else
      component.set_access(ID_default);
  }
}

/// Register in the \p symbol_table new symbols for the objects
/// java::array[X] where X is byte, float, int, char...
void java_bytecode_convert_classt::add_array_types(symbol_tablet &symbol_table)
{
  const std::string letters="ijsbcfdza";

  for(const char l : letters)
  {
    symbol_typet symbol_type=
      to_symbol_type(java_array_type(l).subtype());

    const irep_idt &symbol_type_identifier=symbol_type.get_identifier();
    if(symbol_table.has_symbol(symbol_type_identifier))
      return;

    struct_typet struct_type;
    // we have the base class, java.lang.Object, length and data
    // of appropriate type
    struct_type.set_tag(symbol_type_identifier);

    struct_type.components().reserve(3);
    struct_typet::componentt
      comp0("@java.lang.Object", symbol_typet("java::java.lang.Object"));
    comp0.set_pretty_name("@java.lang.Object");
    comp0.set_base_name("@java.lang.Object");
    struct_type.components().push_back(comp0);

    struct_typet::componentt comp1("length", java_int_type());
    comp1.set_pretty_name("length");
    comp1.set_base_name("length");
    struct_type.components().push_back(comp1);

    struct_typet::componentt
      comp2("data", java_reference_type(java_type_from_char(l)));
    comp2.set_pretty_name("data");
    comp2.set_base_name("data");
    struct_type.components().push_back(comp2);

    INVARIANT(
      is_valid_java_array(struct_type),
      "Constructed a new type representing a Java Array "
      "object that doesn't match expectations");

    symbolt symbol;
    symbol.name=symbol_type_identifier;
    symbol.base_name=symbol_type.get(ID_C_base_name);
    symbol.is_type=true;
    symbol.type=struct_type;
    symbol_table.add(symbol);

    // Also provide a clone method:
    // ----------------------------

    const irep_idt clone_name=
      id2string(symbol_type_identifier)+".clone:()Ljava/lang/Object;";
    code_typet clone_type;
    clone_type.return_type()=
      java_reference_type(symbol_typet("java::java.lang.Object"));
    code_typet::parametert this_param;
    this_param.set_identifier(id2string(clone_name)+"::this");
    this_param.set_base_name("this");
    this_param.set_this();
    this_param.type()=java_reference_type(symbol_type);
    clone_type.parameters().push_back(this_param);

    parameter_symbolt this_symbol;
    this_symbol.name=this_param.get_identifier();
    this_symbol.base_name=this_param.get_base_name();
    this_symbol.pretty_name=this_symbol.base_name;
    this_symbol.type=this_param.type();
    this_symbol.mode=ID_java;
    symbol_table.add(this_symbol);

    const irep_idt local_name=
      id2string(clone_name)+"::cloned_array";
    auxiliary_symbolt local_symbol;
    local_symbol.name=local_name;
    local_symbol.base_name="cloned_array";
    local_symbol.pretty_name=local_symbol.base_name;
    local_symbol.type=java_reference_type(symbol_type);
    local_symbol.mode=ID_java;
    symbol_table.add(local_symbol);
    const auto &local_symexpr=local_symbol.symbol_expr();

    code_blockt clone_body;

    code_declt declare_cloned(local_symexpr);
    clone_body.move_to_operands(declare_cloned);

    side_effect_exprt java_new_array(
      ID_java_new_array,
      java_reference_type(symbol_type));
    dereference_exprt old_array(this_symbol.symbol_expr(), symbol_type);
    dereference_exprt new_array(local_symexpr, symbol_type);
    member_exprt old_length(old_array, comp1.get_name(), comp1.type());
    java_new_array.copy_to_operands(old_length);
    code_assignt create_blank(local_symexpr, java_new_array);
    clone_body.move_to_operands(create_blank);


    member_exprt old_data(old_array, comp2.get_name(), comp2.type());
    member_exprt new_data(new_array, comp2.get_name(), comp2.type());

    /*
      // TODO use this instead of a loop.
    codet array_copy;
    array_copy.set_statement(ID_array_copy);
    array_copy.move_to_operands(new_data);
    array_copy.move_to_operands(old_data);
    clone_body.move_to_operands(array_copy);
    */

    // Begin for-loop to replace:

    const irep_idt index_name=
      id2string(clone_name)+"::index";
    auxiliary_symbolt index_symbol;
    index_symbol.name=index_name;
    index_symbol.base_name="index";
    index_symbol.pretty_name=index_symbol.base_name;
    index_symbol.type=comp1.type();
    index_symbol.mode=ID_java;
    symbol_table.add(index_symbol);
    const auto &index_symexpr=index_symbol.symbol_expr();

    code_declt declare_index(index_symexpr);
    clone_body.move_to_operands(declare_index);

    code_fort copy_loop;

    copy_loop.init()=
      code_assignt(index_symexpr, from_integer(0, index_symexpr.type()));
    copy_loop.cond()=
      binary_relation_exprt(index_symexpr, ID_lt, old_length);

    side_effect_exprt inc(ID_assign);
    inc.operands().resize(2);
    inc.op0()=index_symexpr;
    inc.op1()=plus_exprt(index_symexpr, from_integer(1, index_symexpr.type()));
    copy_loop.iter()=inc;

    dereference_exprt old_cell(
      plus_exprt(old_data, index_symexpr), old_data.type().subtype());
    dereference_exprt new_cell(
      plus_exprt(new_data, index_symexpr), new_data.type().subtype());
    code_assignt copy_cell(new_cell, old_cell);
    copy_loop.body()=copy_cell;

    // End for-loop
    clone_body.move_to_operands(copy_loop);

    member_exprt new_base_class(new_array, comp0.get_name(), comp0.type());
    address_of_exprt retval(new_base_class);
    code_returnt return_inst(retval);
    clone_body.move_to_operands(return_inst);

    symbolt clone_symbol;
    clone_symbol.name=clone_name;
    clone_symbol.pretty_name=
      id2string(symbol_type_identifier)+".clone:()";
    clone_symbol.base_name="clone";
    clone_symbol.type=clone_type;
    clone_symbol.value=clone_body;
    clone_symbol.mode=ID_java;
    symbol_table.add(clone_symbol);
  }
}

bool java_bytecode_convert_class(
  const java_bytecode_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  method_bytecodet &method_bytecode,
  lazy_methods_modet lazy_methods_mode,
  java_string_library_preprocesst &string_preprocess)
{
  java_bytecode_convert_classt java_bytecode_convert_class(
    symbol_table,
    message_handler,
    max_array_length,
    method_bytecode,
    lazy_methods_mode,
    string_preprocess);

  try
  {
    java_bytecode_convert_class(parse_tree);
    return false;
  }

  catch(int)
  {
  }

  catch(const char *e)
  {
    java_bytecode_convert_class.error() << e << messaget::eom;
  }

  catch(const std::string &e)
  {
    java_bytecode_convert_class.error() << e << messaget::eom;
  }

  return true;
}

/// For a given generic type parameter, check if there is a parameter in the
/// given vector of replacement parameters with a matching name. If yes,
/// replace the identifier of the parameter at hand by the identifier of
/// the matching parameter.
/// Example: if \p parameter has identifier `java::Outer$Inner::T` and
/// there is a replacement parameter with identifier `java::Outer::T`, the
/// identifier of \p parameter gets set to `java::Outer::T`.
/// \param parameter
/// \param replacement_parameters vector of generic parameters (only viable
///   ones, i.e., only those that can actually appear here such as generic
///   parameters of outer classes of the class specified by the prefix of \p
///   parameter identifier)
static void find_and_replace_parameter(
  java_generic_parametert &parameter,
  const std::vector<java_generic_parametert> &replacement_parameters)
{
  // get the name of the parameter, e.g., `T` from `java::Class::T`
  const std::string &parameter_full_name =
    as_string(parameter.type_variable_ref().get_identifier());
  const std::string &parameter_name =
    parameter_full_name.substr(parameter_full_name.rfind("::") + 2);

  // check if there is a replacement parameter with the same name
  const auto replacement_parameter_p = std::find_if(
    replacement_parameters.begin(),
    replacement_parameters.end(),
    [&parameter_name](const java_generic_parametert &replacement_param)
    {
      const std::string &replacement_parameter_full_name =
        as_string(replacement_param.type_variable().get_identifier());
      return parameter_name.compare(
               replacement_parameter_full_name.substr(
                 replacement_parameter_full_name.rfind("::") + 2)) == 0;
    });

  // if a replacement parameter was found, update the identifier
  if(replacement_parameter_p != replacement_parameters.end())
  {
    const std::string &replacement_parameter_full_name =
      as_string(replacement_parameter_p->type_variable().get_identifier());

    // the replacement parameter is a viable one, i.e., it comes from an outer
    // class
    PRECONDITION(
      parameter_full_name.substr(0, parameter_full_name.rfind("::"))
        .compare(
          replacement_parameter_full_name.substr(
            0, replacement_parameter_full_name.rfind("::"))) > 0);

    parameter.type_variable_ref().set_identifier(
      replacement_parameter_full_name);
  }
}

/// Recursively find all generic type parameters of a given type and replace
/// their identifiers if matching replacement parameter exist.
/// Example: class `Outer<T>` has an inner class `Inner` that has a field
/// `t` of type `Generic<T>`. This function ensures that the parameter points to
/// `java::Outer::T` instead of `java::Outer$Inner::T`.
/// \param type
/// \param replacement_parameters
static void find_and_replace_parameters(
  typet &type,
  const std::vector<java_generic_parametert> &replacement_parameters)
{
  if(is_java_generic_parameter(type))
  {
    find_and_replace_parameter(
      to_java_generic_parameter(type), replacement_parameters);
  }
  else if(is_java_generic_type(type))
  {
    java_generic_typet &generic_type = to_java_generic_type(type);
    std::vector<reference_typet> &arguments =
      generic_type.generic_type_arguments();
    for(auto &argument : arguments)
    {
      find_and_replace_parameters(argument, replacement_parameters);
    }
  }
  else if(is_java_generic_symbol_type(type))
  {
    java_generic_symbol_typet &generic_base = to_java_generic_symbol_type(type);
    std::vector<reference_typet> &gen_types = generic_base.generic_types();
    for(auto &gen_type : gen_types)
    {
      find_and_replace_parameters(gen_type, replacement_parameters);
    }
  }
}

/// Checks if the class is implicitly generic, i.e., it is an inner class of
/// any generic class. All uses of the implicit generic type parameters within
/// the inner class are updated to point to the type parameters of the
/// corresponding outer classes.
/// \param class_name
/// \param symbol_table
void mark_java_implicitly_generic_class_type(
  const irep_idt &class_name,
  symbol_tablet &symbol_table)
{
  const std::string qualified_class_name = "java::" + id2string(class_name);
  PRECONDITION(symbol_table.has_symbol(qualified_class_name));
  symbolt &class_symbol = symbol_table.get_writeable_ref(qualified_class_name);
  java_class_typet &class_type = to_java_class_type(class_symbol.type);

  // the class must be an inner non-static class, i.e., have a field this$*
  // TODO this should be simplified once static inner classes are marked
  // during parsing
  bool no_this_field = std::none_of(
    class_type.components().begin(),
    class_type.components().end(),
    [](const struct_union_typet::componentt &component)
    {
      return id2string(component.get_name()).substr(0, 5) == "this$";
    });
  if(no_this_field)
  {
    return;
  }

  // create a vector of all generic type parameters of all outer classes, in
  // the order from the outer-most inwards
  std::vector<java_generic_parametert> implicit_generic_type_parameters;
  std::string::size_type outer_class_delimiter =
    qualified_class_name.rfind("$");
  while(outer_class_delimiter != std::string::npos)
  {
    std::string outer_class_name =
      qualified_class_name.substr(0, outer_class_delimiter);
    if(symbol_table.has_symbol(outer_class_name))
    {
      const symbolt &outer_class_symbol =
        symbol_table.lookup_ref(outer_class_name);
      const java_class_typet &outer_class_type =
        to_java_class_type(outer_class_symbol.type);
      if(is_java_generic_class_type(outer_class_type))
      {
        const auto &outer_generic_type_parameters =
          to_java_generic_class_type(outer_class_type).generic_types();
        implicit_generic_type_parameters.insert(
          implicit_generic_type_parameters.begin(),
          outer_generic_type_parameters.begin(),
          outer_generic_type_parameters.end());
      }
      outer_class_delimiter = outer_class_name.rfind("$");
    }
    else
    {
      throw missing_outer_class_symbol_exceptiont(
        outer_class_name, qualified_class_name);
    }
  }

  // if there are any implicit generic type parameters, mark the class
  // implicitly generic and update identifiers of type parameters used in fields
  if(!implicit_generic_type_parameters.empty())
  {
    class_symbol.type = java_implicitly_generic_class_typet(
      class_type, implicit_generic_type_parameters);

    for(auto &field : class_type.components())
    {
      find_and_replace_parameters(
        field.type(), implicit_generic_type_parameters);
    }

    for(auto &base : class_type.bases())
    {
      find_and_replace_parameters(
        base.type(), implicit_generic_type_parameters);
    }
  }
}

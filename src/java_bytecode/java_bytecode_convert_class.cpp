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

class java_bytecode_convert_classt:public messaget
{
public:
  java_bytecode_convert_classt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    size_t _max_array_length,
    lazy_methodst& _lazy_methods,
    lazy_methods_modet _lazy_methods_mode,
    java_string_library_preprocesst &_string_preprocess):
    messaget(_message_handler),
    symbol_table(_symbol_table),
    max_array_length(_max_array_length),
    lazy_methods(_lazy_methods),
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
  lazy_methodst &lazy_methods;
  lazy_methods_modet lazy_methods_mode;
  java_string_library_preprocesst &string_preprocess;

  // conversion
  void convert(const classt &c);
  void convert(symbolt &class_symbol, const fieldt &f);

  // see definition below for more info
  static void add_array_types(symbol_tablet &symbol_table);
};

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
    symbol_typet base("java::"+id2string(c.extends));
    class_type.add_base(base);
    class_typet::componentt base_class_field;
    base_class_field.type()=base;
    base_class_field.set_name("@"+id2string(c.extends));
    base_class_field.set_base_name("@"+id2string(c.extends));
    base_class_field.set_pretty_name("@"+id2string(c.extends));
    class_type.components().push_back(base_class_field);
  }

  // interfaces are recorded as bases
  for(const auto &interface : c.implements)
  {
    symbol_typet base("java::"+id2string(interface));
    class_type.add_base(base);
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
    lazy_methods[method_identifier]=std::make_pair(class_symbol, &method);
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

    /// this is for a field that holds a generic type, wither with instantiated
    /// or with free type variables, e.g., `List<T> l;` or `List<Integer> l;`
    else if(is_java_generic_type(field_type))
    {
      java_generic_typet &with_gen_type=
        to_java_generic_type(field_type);
#ifdef DEBUG
      std::cout << "fieldtype: generic container type "
                << std::to_string(with_gen_type.generic_type_variables().size())
                << " type " << with_gen_type.id()
                << " name " << f.name
                << " subtype id " << with_gen_type.subtype().id() << "\n";
#endif
      field_type=with_gen_type;
    }

    /// This case is not possible, a field is either a non-instantiated type
    /// variable or a generics container type.
    INVARIANT(
      !is_java_generic_inst_parameter(field_type),
      "Cannot be an instantiated type variable here.");
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
  lazy_methodst &lazy_methods,
  lazy_methods_modet lazy_methods_mode,
  java_string_library_preprocesst &string_preprocess)
{
  java_bytecode_convert_classt java_bytecode_convert_class(
    symbol_table,
    message_handler,
    max_array_length,
    lazy_methods,
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

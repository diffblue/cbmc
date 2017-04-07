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

#include <util/c_types.h>
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
    bool _string_refinement_enabled,
    const character_refine_preprocesst &_character_preprocess):
    messaget(_message_handler),
    symbol_table(_symbol_table),
    max_array_length(_max_array_length),
    lazy_methods(_lazy_methods),
    lazy_methods_mode(_lazy_methods_mode),
    string_refinement_enabled(_string_refinement_enabled),
    character_preprocess(_character_preprocess)
  {
  }

  void operator()(const java_bytecode_parse_treet &parse_tree)
  {
    add_array_types();

    if(parse_tree.loading_successful)
      convert(parse_tree.parsed_class);
    else if(string_refinement_enabled &&
            parse_tree.parsed_class.name=="java.lang.String")
      add_string_type();
    else
      generate_class_stub(parse_tree.parsed_class.name);
  }

  typedef java_bytecode_parse_treet::classt classt;
  typedef java_bytecode_parse_treet::fieldt fieldt;

protected:
  symbol_tablet &symbol_table;
  const size_t max_array_length;
  lazy_methodst &lazy_methods;
  lazy_methods_modet lazy_methods_mode;
  bool string_refinement_enabled;
  character_refine_preprocesst character_preprocess;

  // conversion
  void convert(const classt &c);
  void convert(symbolt &class_symbol, const fieldt &f);

  void generate_class_stub(const irep_idt &class_name);
  void add_array_types();
  void add_string_type();
};

void java_bytecode_convert_classt::convert(const classt &c)
{
  std::string qualified_classname="java::"+id2string(c.name);
  if(symbol_table.has_symbol(qualified_classname))
  {
    debug() << "Skip class " << c.name << " (already loaded)" << eom;
    return;
  }

  class_typet class_type;

  class_type.set_tag(c.name);
  class_type.set(ID_base_name, c.name);
  if(c.is_enum)
    class_type.set(
      ID_java_enum_static_unwind,
      std::to_string(c.enum_elements+1));

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
  if(symbol_table.move(new_symbol, class_symbol))
  {
    error() << "failed to add class symbol " << new_symbol.name << eom;
    throw 0;
  }

  // now do fields
  for(const auto &field : c.fields)
    convert(*class_symbol, field);

  // now do methods
  for(const auto &method : c.methods)
  {
    const irep_idt method_identifier=
      id2string(qualified_classname)+
      "."+id2string(method.name)+
      ":"+method.signature;
    // Always run the lazy pre-stage, as it symbol-table
    // registers the function.
    java_bytecode_convert_method_lazy(
      *class_symbol,
      method_identifier,
      method,
      symbol_table);
    if(lazy_methods_mode==LAZY_METHODS_MODE_EAGER)
    {
      // Upgrade to a fully-realized symbol now:
      java_bytecode_convert_method(
        *class_symbol,
        method,
        symbol_table,
        get_message_handler(),
        max_array_length,
        character_preprocess);
    }
    else
    {
      // Wait for our caller to decide what needs elaborating.
      lazy_methods[method_identifier]=std::make_pair(class_symbol, &method);
    }
  }

  // is this a root class?
  if(c.extends.empty())
    java_root_class(*class_symbol);
}

void java_bytecode_convert_classt::generate_class_stub(
  const irep_idt &class_name)
{
  class_typet class_type;

  class_type.set_tag(class_name);
  class_type.set(ID_base_name, class_name);

  class_type.set(ID_incomplete_class, true);

  // produce class symbol
  symbolt new_symbol;
  new_symbol.base_name=class_name;
  new_symbol.pretty_name=class_name;
  new_symbol.name="java::"+id2string(class_name);
  class_type.set(ID_name, new_symbol.name);
  new_symbol.type=class_type;
  new_symbol.mode=ID_java;
  new_symbol.is_type=true;

  symbolt *class_symbol;

  if(symbol_table.move(new_symbol, class_symbol))
  {
    warning() << "stub class symbol " << new_symbol.name
              << " already exists" << eom;
  }
  else
  {
    // create the class identifier etc
    java_root_class(*class_symbol);
  }
}

void java_bytecode_convert_classt::convert(
  symbolt &class_symbol,
  const fieldt &f)
{
  typet field_type=java_type_from_string(f.signature);

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
      symbol_table.symbols.erase(s_it); // erase, we stubbed it

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

void java_bytecode_convert_classt::add_array_types()
{
  const std::string letters="ijsbcfdza";

  for(const char l : letters)
  {
    symbol_typet symbol_type=
      to_symbol_type(java_array_type(l).subtype());

    struct_typet struct_type;
    // we have the base class, java.lang.Object, length and data
    // of appropriate type
    struct_type.set_tag(symbol_type.get_identifier());

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
      comp2("data", pointer_type(java_type_from_char(l)));
    comp2.set_pretty_name("data");
    comp2.set_base_name("data");
    struct_type.components().push_back(comp2);

    symbolt symbol;
    symbol.name=symbol_type.get_identifier();
    symbol.base_name=symbol_type.get(ID_C_base_name);
    symbol.is_type=true;
    symbol.type=struct_type;
    symbol_table.add(symbol);
  }
}

bool java_bytecode_convert_class(
  const java_bytecode_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  lazy_methodst &lazy_methods,
  lazy_methods_modet lazy_methods_mode,
  bool string_refinement_enabled,
  const character_refine_preprocesst &character_preprocess)
{
  java_bytecode_convert_classt java_bytecode_convert_class(
    symbol_table,
    message_handler,
    max_array_length,
    lazy_methods,
    lazy_methods_mode,
    string_refinement_enabled,
    character_preprocess);

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

/// Implements the java.lang.String type in the case that we provide an internal
/// implementation.
void java_bytecode_convert_classt::add_string_type()
{
  class_typet string_type;
  string_type.set_tag("java.lang.String");
  string_type.components().resize(3);
  string_type.components()[0].set_name("@java.lang.Object");
  string_type.components()[0].set_pretty_name("@java.lang.Object");
  string_type.components()[0].type()=symbol_typet("java::java.lang.Object");
  string_type.components()[1].set_name("length");
  string_type.components()[1].set_pretty_name("length");
  string_type.components()[1].type()=java_int_type();
  string_type.components()[2].set_name("data");
  string_type.components()[2].set_pretty_name("data");
  // Use a pointer-to-unbounded-array instead of a pointer-to-char.
  // Saves some casting in the string refinement algorithm but may
  // be unnecessary.
  string_type.components()[2].type()=pointer_type(
    array_typet(java_char_type(), infinity_exprt(java_int_type())));
  string_type.add_base(symbol_typet("java::java.lang.Object"));

  symbolt string_symbol;
  string_symbol.name="java::java.lang.String";
  string_symbol.base_name="java.lang.String";
  string_symbol.type=string_type;
  string_symbol.is_type=true;

  symbol_table.add(string_symbol);

  // Also add a stub of `String.equals` so that remove-virtual-functions
  // generates a check for Object.equals vs. String.equals.
  // No need to fill it in, as pass_preprocess will replace the calls again.
  symbolt string_equals_symbol;
  string_equals_symbol.name=
    "java::java.lang.String.equals:(Ljava/lang/Object;)Z";
  string_equals_symbol.base_name="java.lang.String.equals";
  string_equals_symbol.pretty_name="java.lang.String.equals";
  string_equals_symbol.mode=ID_java;

  code_typet string_equals_type;
  string_equals_type.return_type()=java_boolean_type();
  code_typet::parametert thisparam;
  thisparam.set_this();
  thisparam.type()=java_reference_type(symbol_typet(string_symbol.name));
  code_typet::parametert otherparam;
  otherparam.type()=java_reference_type(symbol_typet("java::java.lang.Object"));
  string_equals_type.parameters().push_back(thisparam);
  string_equals_type.parameters().push_back(otherparam);
  string_equals_symbol.type=std::move(string_equals_type);

  symbol_table.add(string_equals_symbol);
}

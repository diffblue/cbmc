/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include "java_bytecode_convert_class.h"
#include "java_root_class.h"
#include "java_types.h"
#include "java_bytecode_convert_method.h"

#include <util/std_expr.h>
#include <util/expr_util.h>

namespace {
class java_bytecode_convert_classt:public messaget
{
public:
  java_bytecode_convert_classt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    const bool &_disable_runtime_checks,
    int _max_array_length):
    messaget(_message_handler),
    symbol_table(_symbol_table),
    disable_runtime_checks(_disable_runtime_checks),
    max_array_length(_max_array_length)
  {
  }

  void operator()(const java_bytecode_parse_treet &parse_tree)
  {
    add_array_types();

    if(parse_tree.loading_successful)
      convert(parse_tree.parsed_class);
    else
      generate_class_stub(parse_tree.parsed_class.name);
  }

  typedef java_bytecode_parse_treet::classt classt;
  typedef java_bytecode_parse_treet::fieldt fieldt;

protected:
  symbol_tablet &symbol_table;
  const bool &disable_runtime_checks;
  int max_array_length;

  // conversion
  void convert(const classt &c);
  void convert(symbolt &class_symbol, const fieldt &f);

  void generate_class_stub(const irep_idt &class_name);
  void add_array_types();
};
}

/*******************************************************************\

Function: java_bytecode_convert_classt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_convert_classt::convert(const classt &c)
{
  class_typet class_type;

  class_type.set_tag(c.name);
  class_type.set(ID_base_name, c.name);

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
  new_symbol.name="java::"+id2string(c.name);
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
    java_bytecode_convert_method(
      *class_symbol, method, symbol_table, get_message_handler(),
      disable_runtime_checks, max_array_length);

  // is this a root class?
  if(c.extends.empty())
    java_root_class(*class_symbol);
}

/*******************************************************************\

Function: java_bytecode_convert_classt::generate_class_stub

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_convert_classt::generate_class_stub(const irep_idt &class_name)
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
    warning() << "stub class symbol "+id2string(new_symbol.name)+" already exists";
  }
  else
  {
    // create the class identifier etc
    java_root_class(*class_symbol);
  }
}

/*******************************************************************\

Function: java_bytecode_convert_classt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    new_symbol.pretty_name=id2string(class_symbol.pretty_name)+"."+id2string(f.name);
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;
    new_symbol.value=gen_zero(field_type);

    // Do we have the static field symbol already?
    const auto s_it=symbol_table.symbols.find(new_symbol.name);
    if(s_it!=symbol_table.symbols.end())
      symbol_table.symbols.erase(s_it); // erase, we stubbed it

    if(symbol_table.add(new_symbol))
    {
      error() << "failed to add static field symbol" << eom;
      throw 0;
    }
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
  }
}

/*******************************************************************\

Function: java_bytecode_convert_classt::add_array_types

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
<<<<<<< d8b7f7885387d26f7031f56b237aa96e25733f6d

    struct_type.components().reserve(3);
    struct_typet::componentt
      comp0("@java.lang.Object", symbol_typet("java::java.lang.Object"));
    struct_type.components().push_back(comp0);

    struct_typet::componentt comp1("length", java_int_type());
    struct_type.components().push_back(comp1);

    struct_typet::componentt
      comp2("data", pointer_typet(java_type_from_char(l)));
    struct_type.components().push_back(comp2);
=======
    struct_type.components().resize(3);
    struct_type.components()[0].set_name("@java.lang.Object");
    struct_type.components()[0].type()=symbol_typet("java::java.lang.Object");
    struct_type.components()[1].set_name("length");
    struct_type.components()[1].set_pretty_name("length");
    struct_type.components()[1].type()=java_int_type();
    struct_type.components()[2].set_name("data");
    struct_type.components()[2].set_pretty_name("data");
    struct_type.components()[2].type()=
      pointer_typet(java_type_from_char(letters[i]));
>>>>>>> class conversion runtime checks / array handling

    symbolt symbol;
    symbol.name=symbol_type.get_identifier();
    symbol.base_name=symbol_type.get(ID_C_base_name);
    symbol.is_type=true;
    symbol.type=struct_type;
    symbol_table.add(symbol);
  }
}

/*******************************************************************\

Function: java_bytecode_convert_class

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_convert_class(
  const java_bytecode_parse_treet &parse_tree,
  const bool &disable_runtime_checks,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  int max_array_length)
{
  java_bytecode_convert_classt java_bytecode_convert_class(
                   symbol_table,
                   message_handler,
                   disable_runtime_checks,
                   max_array_length);

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

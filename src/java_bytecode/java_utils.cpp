/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_utils.h"

#include <util/invariant.h>
#include <util/message.h>
#include <util/prefix.h>
#include <util/std_types.h>
#include <util/string_utils.h>

#include "java_root_class.h"
#include "java_types.h"

bool java_is_array_type(const typet &type)
{
  if(type.id()!=ID_struct)
    return false;
  return has_prefix(id2string(
    to_struct_type(type).get_tag()),
                    "java::array[");
}

unsigned java_local_variable_slots(const typet &t)
{
  unsigned bitwidth;

  bitwidth=t.get_unsigned_int(ID_width);
  INVARIANT(
    bitwidth==0 ||
    bitwidth==8 ||
    bitwidth==16 ||
    bitwidth==32 ||
    bitwidth==64,
    "all types constructed in java_types.cpp encode JVM types "
    "with these bit widths");
  INVARIANT(
    bitwidth!=0 || t.id()==ID_pointer,
    "if bitwidth is 0, then this a reference to a class, which is 1 slot");

  return bitwidth==64 ? 2 : 1;
}

unsigned java_method_parameter_slots(const code_typet &t)
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
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
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
    messaget message(message_handler);
    message.warning() <<
      "stub class symbol " <<
      new_symbol.name <<
      " already exists" << messaget::eom;
  }
  else
  {
    // create the class identifier etc
    java_root_class(*class_symbol);
  }
}

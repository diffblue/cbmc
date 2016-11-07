/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_utils.h"

#include "java_root_class.h"
#include "java_types.h"

#include <util/invariant.h>
#include <util/message.h>
#include <util/prefix.h>
#include <util/std_types.h>
#include <util/string_utils.h>

#include <set>

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

  // Even on a 64-bit platform, Java pointers occupy one slot:
  if(t.id()==ID_pointer)
    return 1;

  unsigned bitwidth;

  bitwidth=t.get_unsigned_int(ID_width);
  INVARIANT(
    bitwidth==8 ||
    bitwidth==16 ||
    bitwidth==32 ||
    bitwidth==64,
    "all types constructed in java_types.cpp encode JVM types "
    "with these bit widths");

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
  const symbol_tablet &symbol_table,
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

dereference_exprt checked_dereference(const exprt &expr, const typet &type)
{
  dereference_exprt result(expr, type);
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
/// start the search
/// \param open_char: the opening delimiter
/// \param close_char: the closing delimiter
/// \returns the index of the matching corresponding closing delimiter in \p src
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
    if(src[c_pos]=='<')
      depth++;
    else if(src[c_pos]=='>')
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

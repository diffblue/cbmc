/*******************************************************************\

Module: String expressions for the string solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_expr.h>

unsigned string_exprt::next_symbol_id=1;

/*******************************************************************\

Function: string_exprt::fresh_symbol

  Inputs: a prefix and a type

 Outputs: a symbol of type tp whose name starts with
          "string_refinement#" followed by prefix

 Purpose: generate a new symbol expression of the given type with some prefix

\*******************************************************************/

symbol_exprt string_exprt::fresh_symbol(
  const irep_idt &prefix, const typet &type)
{
  std::ostringstream buf;
  buf << "string_refinement#" << prefix << "#" << (next_symbol_id++);
  irep_idt name(buf.str());
  return symbol_exprt(name, type);
}

/*******************************************************************\

Constructor: string_exprt

  Inputs: a type for characters

 Purpose: construct a string expression whose length and content are new
          variables

\*******************************************************************/

string_exprt::string_exprt(typet char_type):
  struct_exprt(refined_string_typet(char_type))
{
  refined_string_typet t(char_type);
  symbol_exprt length=
    fresh_symbol("string_length", refined_string_typet::index_type());
  symbol_exprt content=fresh_symbol("string_content", t.get_content_type());
  move_to_operands(length, content);
}


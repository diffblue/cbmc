/** -*- C++ -*- *****************************************************\

Module: String expressions for PASS algorithm
        (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_expr.h>

unsigned string_exprt::next_symbol_id = 1;

symbol_exprt string_exprt::fresh_symbol
(const irep_idt &prefix, const typet &tp)
{
  std::ostringstream buf;
  buf << "string_refinement#" << prefix << "#" << (next_symbol_id++);
  std::string s = buf.str();
  irep_idt name(s.c_str());
  return symbol_exprt(name, tp);
}

string_exprt::string_exprt(unsignedbv_typet char_type)
  : struct_exprt(refined_string_typet(char_type))
{
  refined_string_typet t(char_type);
  symbol_exprt length=
    fresh_symbol("string_length", refined_string_typet::index_type());
  symbol_exprt content=fresh_symbol("string_content", t.get_content_type());
  move_to_operands(length, content);
}



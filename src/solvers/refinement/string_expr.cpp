/** -*- C++ -*- *****************************************************\

Module: String expressions for PASS algorithm
        (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_expr.h>
//#include <ansi-c/string_constant.h>
//#include <java_bytecode/java_types.h>

exprt index_zero = refined_string_typet::index_zero();
unsigned string_exprt::next_symbol_id = 1;

symbol_exprt string_exprt::fresh_symbol(const irep_idt &prefix,
					  const typet &tp)
{
  std::ostringstream buf;
  buf << "string_refinement#" << prefix << "#" << (next_symbol_id++);
  std::string s = buf.str();
  irep_idt name(s.c_str());
  return symbol_exprt(name, tp);
}

constant_exprt constant_of_nat(int i,int width, typet t) {
  return constant_exprt(integer2binary(i,width), t);
}

string_exprt::string_exprt(unsignedbv_typet char_type) : struct_exprt(refined_string_typet(char_type))
{
  refined_string_typet t(char_type);
  symbol_exprt length = fresh_symbol("string_length",refined_string_typet::index_type());
  symbol_exprt content = fresh_symbol("string_content",t.get_content_type());
  move_to_operands(length,content);
}



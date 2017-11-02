/*******************************************************************\

Module: Generates string constraints for constant strings

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for constant strings

#include <solvers/refinement/string_constraint_generator.h>

#include <ansi-c/string_constant.h>
#include <util/prefix.h>
#include <util/unicode.h>

/// Add axioms ensuring that the provided string expression and constant are
/// equal.
/// \param res: array of characters for the result
/// \param sval: a string constant
/// \return integer expression equal to zero
exprt string_constraint_generatort::add_axioms_for_constant(
  const array_string_exprt &res,
  irep_idt sval)
{
  const typet &index_type = res.length().type();
  const typet &char_type = res.content().type().subtype();
  std::string c_str=id2string(sval);
  std::wstring str;

/// \todo We should have a special treatment for java strings when the
/// conversion function is available:
#if 0
  if(mode==ID_java)
    str=utf8_to_utf16_little_endian(c_str);
  else
#endif
    str=widen(c_str);

  for(std::size_t i=0; i<str.size(); i++)
  {
    const exprt idx = from_integer(i, index_type);
    const exprt c = from_integer(str[i], char_type);
    const equal_exprt lemma(res[idx], c);
    axioms.push_back(lemma);
  }

  const exprt s_length = from_integer(str.size(), index_type);

  axioms.push_back(res.axiom_for_has_length(s_length));
  return from_integer(0, get_return_code_type());
}

/// Add axioms to say that the returned string expression is empty
/// \param f: function application with arguments integer `length` and character
///           pointer `ptr`.
/// \return integer expression equal to zero
exprt string_constraint_generatort::add_axioms_for_empty_string(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 2);
  exprt length = f.arguments()[0];
  axioms.push_back(equal_exprt(length, from_integer(0, length.type())));
  return from_integer(0, get_return_code_type());
}

/// String corresponding to an internal cprover string
///
/// Add axioms ensuring that the returned string expression is equal to the
/// string literal.
/// \todo The name of the function should be changed to reflect what it does.
/// \param f: function application with an argument which is a string literal
/// that is a constant with a string value.
/// \return string expression
exprt string_constraint_generatort::add_axioms_from_literal(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size() == 3); // Bad args to string literal?
  const array_string_exprt res = char_array_of_pointer(args[1], args[0]);
  const exprt &arg = args[2];
  irep_idt sval=to_constant_expr(arg).get_value();
  return add_axioms_for_constant(res, sval);
}

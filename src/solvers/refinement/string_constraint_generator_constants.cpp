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

/// extract java string from symbol expression when they are encoded inside the
/// symbol name
/// \par parameters: a symbol expression representing a java literal
/// \return a string constant
irep_idt string_constraint_generatort::extract_java_string(
  const symbol_exprt &s)
{
  std::string tmp=id2string(s.get_identifier());
  std::string prefix("java::java.lang.String.Literal.");
  assert(has_prefix(tmp, prefix));
  std::string value=tmp.substr(prefix.length());
  return irep_idt(value);
}

/// add axioms saying the returned string expression should be equal to the
/// string constant
/// \par parameters: a string constant
/// \return a string expression
string_exprt string_constraint_generatort::add_axioms_for_constant(
  irep_idt sval, const refined_string_typet &ref_type)
{
  string_exprt res=fresh_string(ref_type);
  std::string c_str=id2string(sval);
  std::wstring str;

  // TODO: we should have a special treatment for java strings when the
  // conversion function is available:
#if 0
  if(mode==ID_java)
    str=utf8_to_utf16_little_endian(c_str);
  else
#endif
    str=widen(c_str);

  for(std::size_t i=0; i<str.size(); i++)
  {
    exprt idx=from_integer(i, ref_type.get_index_type());
    exprt c=from_integer(str[i], ref_type.get_char_type());
    equal_exprt lemma(res[idx], c);
    axioms.push_back(lemma);
  }

  exprt s_length=from_integer(str.size(), ref_type.get_index_type());

  axioms.push_back(res.axiom_for_has_length(s_length));
  return res;
}

/// add axioms to say that the returned string expression is empty
/// \par parameters: function application without argument
/// \return string expression
string_exprt string_constraint_generatort::add_axioms_for_empty_string(
  const function_application_exprt &f)
{
  assert(f.arguments().empty());
  assert(refined_string_typet::is_refined_string_type(f.type()));
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  exprt size=from_integer(0, ref_type.get_index_type());
  const array_typet &content_type=ref_type.get_content_type();
  array_of_exprt empty_array(
    from_integer(0, ref_type.get_content_type().subtype()), content_type);
  string_exprt res(size, empty_array, ref_type);
  return res;
}

/// add axioms to say that the returned string expression is equal to the string
/// literal
/// \par parameters: function application with an argument which is a string
///   literal
/// \return string expression
string_exprt string_constraint_generatort::add_axioms_from_literal(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(args.size()==1); // Bad args to string literal?

  const exprt &arg=args[0];
  irep_idt sval;

  assert(arg.operands().size()==1);
  if(arg.op0().operands().size()==2 &&
     arg.op0().op0().id()==ID_string_constant)
  {
    // C string constant
    const exprt &s=arg.op0().op0();
    sval=to_string_constant(s).get_value();
  }
  else
  {
    // Java string constant
    assert(false); // TODO: Check if used. On the contrary, discard else.
    assert(arg.id()==ID_symbol);
    const exprt &s=arg.op0();

    // It seems the value of the string is lost,
    // we need to recover it from the identifier
    sval=extract_java_string(to_symbol_expr(s));
  }

  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  return add_axioms_for_constant(sval, ref_type);
}

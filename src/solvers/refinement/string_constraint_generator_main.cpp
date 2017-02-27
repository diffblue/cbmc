/*******************************************************************\

Module: Generates string constraints to link results from string functions
        with their arguments. This is inspired by the PASS paper at HVC'13:
        "PASS: String Solving with Parameterized Array and Interval Automaton"
        by Guodong Li and Indradeep Ghosh, which gives examples of constraints
        for several functions.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints to link results from string functions with
///   their arguments. This is inspired by the PASS paper at HVC'13: "PASS:
///   String Solving with Parameterized Array and Interval Automaton" by Guodong
///   Li and Indradeep Ghosh, which gives examples of constraints for several
///   functions.

#include <solvers/refinement/string_constraint_generator.h>

#include <ansi-c/string_constant.h>
#include <java_bytecode/java_types.h>
#include <util/arith_tools.h>
#include <util/pointer_predicates.h>
#include <util/ssa_expr.h>

unsigned string_constraint_generatort::next_symbol_id=1;

/// generate constant character expression with character type.
/// \par parameters: integer representing a character, and a type for
///   characters;
/// we do not use char type here because in some languages
/// (for instance java) characters use more than 8 bits.
/// \return constant expression corresponding to the character.
constant_exprt string_constraint_generatort::constant_char(
  int i, const typet &char_type)
{
  return from_integer(i, char_type);
}

/// generate a new symbol expression of the given type with some prefix
/// \par parameters: a prefix and a type
/// \return a symbol of type tp whose name starts with "string_refinement#"
///   followed by prefix
symbol_exprt string_constraint_generatort::fresh_symbol(
  const irep_idt &prefix, const typet &type)
{
  std::ostringstream buf;
  buf << "string_refinement#" << prefix << "#" << (next_symbol_id++);
  irep_idt name(buf.str());
  return symbol_exprt(name, type);
}

/// generate an index symbol to be used as an universaly quantified variable
/// \par parameters: a prefix
/// \return a symbol of index type whose name starts with the prefix
symbol_exprt string_constraint_generatort::fresh_univ_index(
  const irep_idt &prefix, const typet &type)
{
  return fresh_symbol(prefix, type);
}

/// generate an index symbol which is existentially quantified
/// \par parameters: a prefix
/// \return a symbol of index type whose name starts with the prefix
symbol_exprt string_constraint_generatort::fresh_exist_index(
  const irep_idt &prefix, const typet &type)
{
  symbol_exprt s=fresh_symbol(prefix, type);
  index_symbols.push_back(s);
  return s;
}

/// generate a Boolean symbol which is existentially quantified
/// \par parameters: a prefix
/// \return a symbol of index type whose name starts with the prefix
symbol_exprt string_constraint_generatort::fresh_boolean(
  const irep_idt &prefix)
{
  symbol_exprt b=fresh_symbol(prefix, bool_typet());
  boolean_symbols.push_back(b);
  return b;
}

/// construct a string expression whose length and content are new variables
/// \par parameters: a type for string
/// \return a string expression
string_exprt string_constraint_generatort::fresh_string(
  const refined_string_typet &type)
{
  symbol_exprt length=
    fresh_symbol("string_length", type.get_index_type());
  symbol_exprt content=fresh_symbol("string_content", type.get_content_type());
  return string_exprt(length, content, type);
}

/// obtain a refined string expression corresponding to string variable of
/// string function call
/// \par parameters: an expression of type string
/// \return a string expression that is linked to the argument through axioms
///   that are added to the list
string_exprt string_constraint_generatort::add_axioms_for_string_expr(
  const exprt &unrefined_string)
{
  string_exprt s;

  if(unrefined_string.id()==ID_function_application)
  {
    exprt res=add_axioms_for_function_application(
      to_function_application_expr(unrefined_string));
    s=to_string_expr(res);
  }
  else if(unrefined_string.id()==ID_symbol)
    s=find_or_add_string_of_symbol(to_symbol_expr(unrefined_string));
  else if(unrefined_string.id()==ID_address_of)
  {
    assert(unrefined_string.op0().id()==ID_symbol);
    s=find_or_add_string_of_symbol(to_symbol_expr(unrefined_string.op0()));
  }
  else if(unrefined_string.id()==ID_if)
    s=add_axioms_for_if(to_if_expr(unrefined_string));
  else if(unrefined_string.id()==ID_nondet_symbol ||
          unrefined_string.id()==ID_struct)
  {
    // TODO: for now we ignore non deterministic symbols and struct
  }
  else if(unrefined_string.id()==ID_typecast)
  {
    exprt arg=to_typecast_expr(unrefined_string).op();
    exprt res=add_axioms_for_string_expr(arg);
    s=to_string_expr(res);
  }
  else
  {
    throw "add_axioms_for_string_expr:\n"+unrefined_string.pretty()+
      "\nwhich is not a function application, "+
      "a symbol or an if expression";
  }

  axioms.push_back(
    s.axiom_for_is_longer_than(from_integer(0, s.length().type())));
  return s;
}

/// add axioms for an if expression which should return a string
/// \par parameters: an if expression
/// \return a string expression
string_exprt string_constraint_generatort::add_axioms_for_if(
  const if_exprt &expr)
{
  assert(
    refined_string_typet::is_refined_string_type(expr.true_case().type()));
  string_exprt t=add_axioms_for_string_expr(expr.true_case());
  assert(
    refined_string_typet::is_refined_string_type(expr.false_case().type()));
  string_exprt f=add_axioms_for_string_expr(expr.false_case());
  const refined_string_typet &ref_type=to_refined_string_type(t.type());
  const typet &index_type=ref_type.get_index_type();
  string_exprt res=fresh_string(ref_type);

  axioms.push_back(
    implies_exprt(expr.cond(), res.axiom_for_has_same_length_as(t)));
  symbol_exprt qvar=fresh_univ_index("QA_string_if_true", index_type);
  equal_exprt qequal(res[qvar], t[qvar]);
  axioms.push_back(string_constraintt(qvar, t.length(), expr.cond(), qequal));
  axioms.push_back(
    implies_exprt(not_exprt(expr.cond()), res.axiom_for_has_same_length_as(f)));
  symbol_exprt qvar2=fresh_univ_index("QA_string_if_false", index_type);
  equal_exprt qequal2(res[qvar2], f[qvar2]);
  string_constraintt sc2(qvar2, f.length(), not_exprt(expr.cond()), qequal2);
  axioms.push_back(sc2);
  return res;
}

/// if a symbol represent a string is present in the symbol_to_string table,
/// returns the corresponding string, if the symbol is not yet present, creates
/// a new string with the correct type depending on whether the mode is java or
/// c, adds it to the table and returns it.
/// \par parameters: a symbol expression
/// \return a string expression
string_exprt string_constraint_generatort::find_or_add_string_of_symbol(
  const symbol_exprt &sym)
{
  irep_idt id=sym.get_identifier();
  const refined_string_typet &ref_type=to_refined_string_type(sym.type());
  string_exprt str=fresh_string(ref_type);
  auto entry=symbol_to_string.insert(std::make_pair(id, str));
  return entry.first->second;
}

/// strings contained in this call are converted to objects of type
/// `string_exprt`, through adding axioms. Axioms are then added to enforce that
/// the result corresponds to the function application.
/// \par parameters: an expression containing a function application
/// \return expression corresponding to the result of the function application
exprt string_constraint_generatort::add_axioms_for_function_application(
  const function_application_exprt &expr)
{
  const exprt &name=expr.function();
  assert(name.id()==ID_symbol);

  const irep_idt &id=is_ssa_expr(name)?to_ssa_expr(name).get_object_name():
    to_symbol_expr(name).get_identifier();

  // TODO: improve efficiency of this test by either ordering test by frequency
  // or using a map

  if(id==ID_cprover_char_literal_func)
    return add_axioms_for_char_literal(expr);
  else if(id==ID_cprover_string_length_func)
    return add_axioms_for_length(expr);
  else if(id==ID_cprover_string_equal_func)
    return add_axioms_for_equals(expr);
  else if(id==ID_cprover_string_equals_ignore_case_func)
    return add_axioms_for_equals_ignore_case(expr);
  else if(id==ID_cprover_string_is_empty_func)
    return add_axioms_for_is_empty(expr);
  else if(id==ID_cprover_string_char_at_func)
    return add_axioms_for_char_at(expr);
  else if(id==ID_cprover_string_is_prefix_func)
    return add_axioms_for_is_prefix(expr);
  else if(id==ID_cprover_string_is_suffix_func)
    return add_axioms_for_is_suffix(expr);
  else if(id==ID_cprover_string_startswith_func)
    return add_axioms_for_is_prefix(expr, true);
  else if(id==ID_cprover_string_endswith_func)
    return add_axioms_for_is_suffix(expr, true);
  else if(id==ID_cprover_string_contains_func)
    return add_axioms_for_contains(expr);
  else if(id==ID_cprover_string_hash_code_func)
    return add_axioms_for_hash_code(expr);
  else if(id==ID_cprover_string_index_of_func)
    return add_axioms_for_index_of(expr);
  else if(id==ID_cprover_string_last_index_of_func)
    return add_axioms_for_last_index_of(expr);
  else if(id==ID_cprover_string_parse_int_func)
    return add_axioms_for_parse_int(expr);
  else if(id==ID_cprover_string_to_char_array_func)
    return add_axioms_for_to_char_array(expr);
  else if(id==ID_cprover_string_code_point_at_func)
    return add_axioms_for_code_point_at(expr);
  else if(id==ID_cprover_string_code_point_before_func)
    return add_axioms_for_code_point_before(expr);
  else if(id==ID_cprover_string_code_point_count_func)
    return add_axioms_for_code_point_count(expr);
  else if(id==ID_cprover_string_offset_by_code_point_func)
    return add_axioms_for_offset_by_code_point(expr);
  else if(id==ID_cprover_string_compare_to_func)
    return add_axioms_for_compare_to(expr);
  else if(id==ID_cprover_string_literal_func)
    return add_axioms_from_literal(expr);
  else if(id==ID_cprover_string_concat_func)
    return add_axioms_for_concat(expr);
  else if(id==ID_cprover_string_concat_int_func)
    return add_axioms_for_concat_int(expr);
  else if(id==ID_cprover_string_concat_long_func)
    return add_axioms_for_concat_long(expr);
  else if(id==ID_cprover_string_concat_bool_func)
      return add_axioms_for_concat_bool(expr);
  else if(id==ID_cprover_string_concat_char_func)
    return add_axioms_for_concat_char(expr);
  else if(id==ID_cprover_string_concat_double_func)
    return add_axioms_for_concat_double(expr);
  else if(id==ID_cprover_string_concat_float_func)
    return add_axioms_for_concat_float(expr);
  else if(id==ID_cprover_string_concat_code_point_func)
    return add_axioms_for_concat_code_point(expr);
  else if(id==ID_cprover_string_insert_func)
    return add_axioms_for_insert(expr);
  else if(id==ID_cprover_string_insert_int_func)
    return add_axioms_for_insert_int(expr);
  else if(id==ID_cprover_string_insert_long_func)
    return add_axioms_for_insert_long(expr);
  else if(id==ID_cprover_string_insert_bool_func)
    return add_axioms_for_insert_bool(expr);
  else if(id==ID_cprover_string_insert_char_func)
    return add_axioms_for_insert_char(expr);
  else if(id==ID_cprover_string_insert_double_func)
    return add_axioms_for_insert_double(expr);
  else if(id==ID_cprover_string_insert_float_func)
    return add_axioms_for_insert_float(expr);
  else if(id==ID_cprover_string_insert_char_array_func)
    return add_axioms_for_insert_char_array(expr);
  else if(id==ID_cprover_string_substring_func)
    return add_axioms_for_substring(expr);
  else if(id==ID_cprover_string_trim_func)
    return add_axioms_for_trim(expr);
  else if(id==ID_cprover_string_to_lower_case_func)
    return add_axioms_for_to_lower_case(expr);
  else if(id==ID_cprover_string_to_upper_case_func)
    return add_axioms_for_to_upper_case(expr);
  else if(id==ID_cprover_string_char_set_func)
    return add_axioms_for_char_set(expr);
  else if(id==ID_cprover_string_value_of_func)
    return add_axioms_for_value_of(expr);
  else if(id==ID_cprover_string_empty_string_func)
    return add_axioms_for_empty_string(expr);
  else if(id==ID_cprover_string_copy_func)
    return add_axioms_for_copy(expr);
  else if(id==ID_cprover_string_of_int_func)
    return add_axioms_from_int(expr);
  else if(id==ID_cprover_string_of_int_hex_func)
    return add_axioms_from_int_hex(expr);
  else if(id==ID_cprover_string_of_float_func)
    return add_axioms_from_float(expr);
  else if(id==ID_cprover_string_of_double_func)
    return add_axioms_from_double(expr);
  else if(id==ID_cprover_string_of_long_func)
    return add_axioms_from_long(expr);
  else if(id==ID_cprover_string_of_bool_func)
    return add_axioms_from_bool(expr);
  else if(id==ID_cprover_string_of_char_func)
    return add_axioms_from_char(expr);
  else if(id==ID_cprover_string_of_char_array_func)
    return add_axioms_from_char_array(expr);
  else if(id==ID_cprover_string_set_length_func)
    return add_axioms_for_set_length(expr);
  else if(id==ID_cprover_string_delete_func)
    return add_axioms_for_delete(expr);
  else if(id==ID_cprover_string_delete_char_at_func)
    return add_axioms_for_delete_char_at(expr);
  else if(id==ID_cprover_string_replace_func)
    return add_axioms_for_replace(expr);
  else
  {
    std::string msg(
      "string_constraint_generator::function_application: unknown symbol :");
    msg+=id2string(id);
    throw msg;
  }
}

/// add axioms to say that the returned string expression is equal to the
/// argument of the function application
/// \par parameters: function application with one argument, which is a string
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_copy(
  const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 1)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(s1.type());
  string_exprt res=fresh_string(ref_type);

  // We add axioms:
  // a1 : |res|=|s1|
  // a2 : forall i<|s1|. s1[i]=res[i]

  axioms.push_back(res.axiom_for_has_same_length_as(s1));

  symbol_exprt idx=fresh_univ_index("QA_index_copy", ref_type.get_index_type());
  string_constraintt a2(idx, s1.length(), equal_exprt(s1[idx], res[idx]));
  axioms.push_back(a2);
  return res;
}

/// add axioms corresponding to the String.valueOf([C) java function
/// \par parameters: an expression corresponding to a java object of type char
///   array
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_for_java_char_array(
  const exprt &char_array)
{
  string_exprt res=fresh_string(
    refined_string_typet(java_int_type(), java_char_type()));
  exprt arr=to_address_of_expr(char_array).object();
  exprt len=member_exprt(arr, "length", res.length().type());
  exprt cont=member_exprt(arr, "data", res.content().type());
  res.length()=len;
  res.content()=cont;
  return res;
}

/// add axioms corresponding to the String.length java function
/// \par parameters: function application with one string argument
/// \return a string expression of index type
exprt string_constraint_generatort::add_axioms_for_length(
  const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 1)[0]);
  return str.length();
}

/// add axioms stating that the content of the returned string equals to the
/// content of the array argument, starting at offset and with `count`
/// characters
/// \par parameters: a length expression, an array expression, a offset index,
///   and a
/// count index
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_char_array(
  const exprt &length,
  const exprt &data,
  const exprt &offset,
  const exprt &count)
{
  const typet &char_type=to_array_type(data.type()).subtype();
  const typet &index_type=length.type();
  refined_string_typet ref_type(index_type, char_type);
  string_exprt str=fresh_string(ref_type);

  // We add axioms:
  // a1 : forall q < count. str[q] = data[q+offset]
  // a2 : |str| = count

  symbol_exprt qvar=fresh_univ_index("QA_string_of_char_array", index_type);
  exprt char_in_tab=data;
  assert(char_in_tab.id()==ID_index);
  char_in_tab.op1()=plus_exprt(qvar, offset);

  string_constraintt a1(qvar, count, equal_exprt(str[qvar], char_in_tab));
  axioms.push_back(a1);
  axioms.push_back(equal_exprt(str.length(), count));

  return str;
}

/// add axioms corresponding to the String.<init>:(I[CII) and
/// String.<init>:(I[C) java functions
/// function application with 2 arguments and 2 additional optional
/// \param arguments: length, char array, offset and count
/// \return a new string expression
string_exprt string_constraint_generatort::add_axioms_from_char_array(
  const function_application_exprt &f)
{
  exprt offset;
  exprt count;
  if(f.arguments().size()==4)
  {
    offset=f.arguments()[2];
    count=f.arguments()[3];
  }
  else
  {
    assert(f.arguments().size()==2);
    count=f.arguments()[0];
    offset=from_integer(0, count.type());
  }
  const exprt &tab_length=f.arguments()[0];
  const exprt &data=f.arguments()[1];
  return add_axioms_from_char_array(tab_length, data, offset, count);
}

/// expression true exactly when the index is positive
/// \par parameters: an index expression
/// \return a Boolean expression
exprt string_constraint_generatort::axiom_for_is_positive_index(const exprt &x)
{
  return binary_relation_exprt(
    x, ID_ge, from_integer(0, x.type()));
}

/// add axioms stating that the returned value is equal to the argument
/// \par parameters: function application with one character argument
/// \return a new character expression
exprt string_constraint_generatort::add_axioms_for_char_literal(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(args.size()==1); // there should be exactly 1 argument to char literal

  const exprt &arg=args[0];
  // for C programs argument to char literal should be one string constant
  // of size 1.
  if(arg.operands().size()==1 &&
     arg.op0().operands().size()==1 &&
     arg.op0().op0().operands().size()==2 &&
     arg.op0().op0().op0().id()==ID_string_constant)
  {
    const string_constantt s=to_string_constant(arg.op0().op0().op0());
    irep_idt sval=s.get_value();
    assert(sval.size()==1);
    return from_integer(unsigned(sval[0]), arg.type());
  }
  else
  {
    throw "convert_char_literal unimplemented";
  }
}

/// add axioms stating that the character of the string at the given position is
/// equal to the returned value
/// \par parameters: function application with two arguments: a string and an
///   integer
/// \return a character expression
exprt string_constraint_generatort::add_axioms_for_char_at(
  const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 2)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  symbol_exprt char_sym=fresh_symbol("char", ref_type.get_char_type());
  axioms.push_back(equal_exprt(char_sym, str[args(f, 2)[1]]));
  return char_sym;
}

/// add axioms corresponding to the String.toCharArray java function
/// \par parameters: function application with one string argument
/// \return a char array expression
exprt string_constraint_generatort::add_axioms_for_to_char_array(
  const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 1)[0]);
  return str.content();
}

/// add a correspondence to make sure the symbol points to the same string as
/// the second argument
/// \par parameters: a symbol and a string
void string_constraint_generatort::set_string_symbol_equal_to_expr(
  const symbol_exprt &sym, const exprt &str)
{
  if(str.id()==ID_symbol)
    assign_to_symbol(sym, find_or_add_string_of_symbol(to_symbol_expr(str)));
  else
    assign_to_symbol(sym, add_axioms_for_string_expr(str));
}

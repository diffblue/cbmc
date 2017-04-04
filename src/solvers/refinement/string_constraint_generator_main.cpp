/*******************************************************************\

Module: Generates string constraints to link results from string functions
        with their arguments. This is inspired by the PASS paper at HVC'13:
        "PASS: String Solving with Parameterized Array and Interval Automaton"
        by Guodong Li and Indradeep Ghosh, which gives examples of constraints
        for several functions.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <ansi-c/string_constant.h>
#include <java_bytecode/java_types.h>
#include <solvers/refinement/string_constraint_generator.h>
#include <util/arith_tools.h>
#include <util/pointer_predicates.h>
#include <util/ssa_expr.h>
#include <iostream>

unsigned string_constraint_generatort::next_symbol_id=1;

/*******************************************************************\

Function: string_constraint_generatort::constant_char

  Inputs: integer representing a character, and a type for characters;
          we do not use char type here because in some languages
          (for instance java) characters use more than 8 bits.

 Outputs: constant expression corresponding to the character.

 Purpose: generate constant character expression with character type.

\*******************************************************************/

constant_exprt string_constraint_generatort::constant_char(
  int i, const typet &char_type)
{
  return from_integer(i, char_type);
}

/*******************************************************************\

Function: string_constraint_generator::fresh_symbol

  Inputs: a prefix and a type

 Outputs: a symbol of type tp whose name starts with
          "string_refinement#" followed by prefix

 Purpose: generate a new symbol expression of the given type with some prefix

\*******************************************************************/

symbol_exprt string_constraint_generatort::fresh_symbol(
  const irep_idt &prefix, const typet &type)
{
  std::ostringstream buf;
  buf << "string_refinement#" << prefix << "#" << (next_symbol_id++);
  irep_idt name(buf.str());
  return symbol_exprt(name, type);
}

/*******************************************************************\

Function: string_constraint_generatort::fresh_univ_index

  Inputs: a prefix

 Outputs: a symbol of index type whose name starts with the prefix

 Purpose: generate an index symbol to be used as an universaly quantified
          variable

\*******************************************************************/

symbol_exprt string_constraint_generatort::fresh_univ_index(
  const irep_idt &prefix, const typet &type)
{
  return fresh_symbol(prefix, type);
}

/*******************************************************************\

Function: string_constraint_generatort::fresh_exist_index

  Inputs: a prefix

 Outputs: a symbol of index type whose name starts with the prefix

 Purpose: generate an index symbol which is existentially quantified

\*******************************************************************/

symbol_exprt string_constraint_generatort::fresh_exist_index(
  const irep_idt &prefix, const typet &type)
{
  symbol_exprt s=fresh_symbol(prefix, type);
  index_symbols.push_back(s);
  return s;
}

/*******************************************************************\

Function: string_constraint_generatort::fresh_boolean

  Inputs: a prefix

 Outputs: a symbol of index type whose name starts with the prefix

 Purpose: generate a Boolean symbol which is existentially quantified

\*******************************************************************/

symbol_exprt string_constraint_generatort::fresh_boolean(
  const irep_idt &prefix)
{
  symbol_exprt b=fresh_symbol(prefix, bool_typet());
  boolean_symbols.push_back(b);
  return b;
}

/*******************************************************************\

Function: string_constraint_generatort::plus_exprt_with_overflow_check

 Inputs:
  op1 - First term of the sum
  op2 - Second term of the sum

 Outputs: A plus expression representing the sum of the arguments

 Purpose: Create a plus expression while adding extra constraints to
          axioms in order to prevent overflows.

\*******************************************************************/
plus_exprt string_constraint_generatort::plus_exprt_with_overflow_check(
  const exprt &op1, const exprt &op2)
{
  plus_exprt sum(plus_exprt(op1, op2));

  exprt zero=from_integer(0, op1.type());

  binary_relation_exprt neg1(op1, ID_lt, zero);
  binary_relation_exprt neg2(op2, ID_lt, zero);
  binary_relation_exprt neg_sum(sum, ID_lt, zero);

  // We prevent overflows by adding the following constraint:
  // If the signs of the two operands are the same, then the sign of the sum
  // should also be the same.
  implies_exprt no_overflow(equal_exprt(neg1, neg2),
                            equal_exprt(neg1, neg_sum));

  axioms.push_back(no_overflow);

  return sum;
}

/*******************************************************************\

Function: string_constraint_generatort::fresh_string

  Inputs: a type for string

 Outputs: a string expression

 Purpose: construct a string expression whose length and content are new
          variables

\*******************************************************************/

string_exprt string_constraint_generatort::fresh_string(
  const refined_string_typet &type)
{
  symbol_exprt length=
    fresh_symbol("string_length", type.get_index_type());
  symbol_exprt content=fresh_symbol("string_content", type.get_content_type());
  return string_exprt(length, content, type);
}

/*******************************************************************\

Function: string_constraint_generatort::get_string_expr

  Inputs: an expression of refined string type

 Outputs: a string expression

 Purpose: casts an expression to a string expression, or fetches the
          actual string_exprt in the case of a symbol.

\*******************************************************************/

string_exprt string_constraint_generatort::get_string_expr(const exprt &expr)
{
  assert(refined_string_typet::is_refined_string_type(expr.type()));

  if(expr.id()==ID_symbol)
  {
    return find_or_add_string_of_symbol(
      to_symbol_expr(expr),
      to_refined_string_type(expr.type()));
  }
  else
  {
    return to_string_expr(expr);
  }
}

string_exprt string_constraint_generatort::convert_java_string_to_string_exprt(
    const exprt &jls)
{
  assert(get_mode()==ID_java);
  assert(jls.id()==ID_struct);

  exprt length(to_struct_expr(jls).op1());
  // TODO: Add assertion on the type.
  // assert(length.type()==refined_string_typet::index_type());
  exprt java_content(to_struct_expr(jls).op2());
  if(java_content.id()==ID_address_of)
  {
    java_content=to_address_of_expr(java_content).object();
  }
  else
  {
    java_content=dereference_exprt(java_content, java_content.type());
  }

  refined_string_typet type(java_int_type(), java_char_type());

  return string_exprt(length, java_content, type);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_refined_string

  Inputs: an expression of refined string type

 Outputs: a string expression that is linked to the argument through
          axioms that are added to the list

 Purpose: obtain a refined string expression corresponding to a expression
          of type string

\*******************************************************************/


string_exprt string_constraint_generatort::add_axioms_for_refined_string(
  const exprt &string)
{
  assert(refined_string_typet::is_refined_string_type(string.type()));
  refined_string_typet type=to_refined_string_type(string.type());

  // Function applications should have been removed before
  assert(string.id()!=ID_function_application);

  if(string.id()==ID_symbol)
  {
    const symbol_exprt &sym=to_symbol_expr(string);
    string_exprt s=find_or_add_string_of_symbol(sym, type);
    axioms.push_back(
      s.axiom_for_is_longer_than(from_integer(0, s.length().type())));
    return s;
  }
  else if(string.id()==ID_nondet_symbol)
  {
    string_exprt s=fresh_string(type);
    axioms.push_back(
      s.axiom_for_is_longer_than(from_integer(0, s.length().type())));
    return s;
  }
  else if(string.id()==ID_if)
  {
    return add_axioms_for_if(to_if_expr(string));
  }
  else if(string.id()==ID_struct)
  {
    const string_exprt &s=to_string_expr(string);
    axioms.push_back(
      s.axiom_for_is_longer_than(from_integer(0, s.length().type())));
    return s;
  }
  else
  {
    throw "add_axioms_for_refined_string:\n"+string.pretty()+
      "\nwhich is not a function application, "+
      "a symbol, a struct or an if expression";
  }
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_if

  Inputs: an if expression

 Outputs: a string expression

 Purpose: add axioms for an if expression which should return a string

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_if(
  const if_exprt &expr)
{
  assert(
    refined_string_typet::is_refined_string_type(expr.true_case().type()));
  string_exprt t=get_string_expr(expr.true_case());
  assert(
    refined_string_typet::is_refined_string_type(expr.false_case().type()));
  string_exprt f=get_string_expr(expr.false_case());
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

/*******************************************************************\

Function: string_constraint_generatort::find_or_add_string_of_symbol

  Inputs: a symbol expression

 Outputs: a string expression

 Purpose: if a symbol representing a string is present in the symbol_to_string
          table, returns the corresponding string, if the symbol is not yet
          present, creates a new string with the correct type depending on
          whether the mode is java or c, adds it to the table and returns it.

\*******************************************************************/

string_exprt string_constraint_generatort::find_or_add_string_of_symbol(
  const symbol_exprt &sym, const refined_string_typet &ref_type)
{
  irep_idt id=sym.get_identifier();
  string_exprt str=fresh_string(ref_type);
  auto entry=unresolved_symbols.insert(std::make_pair(id, str));
  return entry.first->second;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_function_application

  Inputs: an expression containing a function application

 Outputs: expression corresponding to the result of the function application

 Purpose: strings contained in this call are converted to objects of type
          `string_exprt`, through adding axioms. Axioms are then added to
          enforce that the result corresponds to the function application.

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_function_application(
  const function_application_exprt &expr)
{
  const exprt &name=expr.function();
  assert(name.id()==ID_symbol);

  const irep_idt &id=is_ssa_expr(name)?to_ssa_expr(name).get_object_name():
    to_symbol_expr(name).get_identifier();

  std::string str_id(id.c_str());

  size_t pos=str_id.find("func_length");
  if(pos!=std::string::npos)
  {
    function_application_exprt new_expr(expr);
    // TODO: This part needs some improvement.
    // Stripping the symbol name is not a very robust process.
    new_expr.function() = symbol_exprt(str_id.substr(0, pos+4));
    assert(get_mode()==ID_java);
    new_expr.type() = refined_string_typet(java_int_type(), java_char_type());

    auto res_it=function_application_cache.insert(std::make_pair(new_expr,
                                                                 nil_exprt()));
    if(res_it.second)
    {
      string_exprt res=to_string_expr(
        add_axioms_for_function_application(new_expr));
      res_it.first->second=res;
      return res.length();
    }
    else
      return to_string_expr(res_it.first->second).length();
  }

  pos = str_id.find("func_data");
  if(pos!=std::string::npos)
  {
    function_application_exprt new_expr(expr);
    new_expr.function() = symbol_exprt(str_id.substr(0, pos+4));
    new_expr.type() = refined_string_typet(java_int_type(), java_char_type());

    auto res_it=function_application_cache.insert(std::make_pair(new_expr,
                                                                 nil_exprt()));
    if(res_it.second)
    {
      string_exprt res=to_string_expr(
        add_axioms_for_function_application(new_expr));
      res_it.first->second=res;
      return res.content();
    }
    else
      return to_string_expr(res_it.first->second).content();
  }

  // TODO: improve efficiency of this test by either ordering test by frequency
  // or using a map

  auto res_it=function_application_cache.find(expr);
  if(res_it!=function_application_cache.end() && res_it->second!=nil_exprt())
    return res_it->second;

  exprt res;

  if(id==ID_cprover_char_literal_func)
    res=add_axioms_for_char_literal(expr);
  else if(id==ID_cprover_string_length_func)
    res=add_axioms_for_length(expr);
  else if(id==ID_cprover_string_equal_func)
    res=add_axioms_for_equals(expr);
  else if(id==ID_cprover_string_equals_ignore_case_func)
    res=add_axioms_for_equals_ignore_case(expr);
  else if(id==ID_cprover_string_is_empty_func)
    res=add_axioms_for_is_empty(expr);
  else if(id==ID_cprover_string_char_at_func)
    res=add_axioms_for_char_at(expr);
  else if(id==ID_cprover_string_is_prefix_func)
    res=add_axioms_for_is_prefix(expr);
  else if(id==ID_cprover_string_is_suffix_func)
    res=add_axioms_for_is_suffix(expr);
  else if(id==ID_cprover_string_startswith_func)
    res=add_axioms_for_is_prefix(expr, true);
  else if(id==ID_cprover_string_endswith_func)
    res=add_axioms_for_is_suffix(expr, true);
  else if(id==ID_cprover_string_contains_func)
    res=add_axioms_for_contains(expr);
  else if(id==ID_cprover_string_hash_code_func)
    res=add_axioms_for_hash_code(expr);
  else if(id==ID_cprover_string_index_of_func)
    res=add_axioms_for_index_of(expr);
  else if(id==ID_cprover_string_last_index_of_func)
    res=add_axioms_for_last_index_of(expr);
  else if(id==ID_cprover_string_parse_int_func)
    res=add_axioms_for_parse_int(expr);
  else if(id==ID_cprover_string_to_char_array_func)
    res=add_axioms_for_to_char_array(expr);
  else if(id==ID_cprover_string_code_point_at_func)
    res=add_axioms_for_code_point_at(expr);
  else if(id==ID_cprover_string_code_point_before_func)
    res=add_axioms_for_code_point_before(expr);
  else if(id==ID_cprover_string_code_point_count_func)
    res=add_axioms_for_code_point_count(expr);
  else if(id==ID_cprover_string_offset_by_code_point_func)
    res=add_axioms_for_offset_by_code_point(expr);
  else if(id==ID_cprover_string_compare_to_func)
    res=add_axioms_for_compare_to(expr);
  else if(id==ID_cprover_string_literal_func)
    res=add_axioms_from_literal(expr);
  else if(id==ID_cprover_string_concat_func)
    res=add_axioms_for_concat(expr);
  else if(id==ID_cprover_string_concat_int_func)
    res=add_axioms_for_concat_int(expr);
  else if(id==ID_cprover_string_concat_long_func)
    res=add_axioms_for_concat_long(expr);
  else if(id==ID_cprover_string_concat_bool_func)
      res=add_axioms_for_concat_bool(expr);
  else if(id==ID_cprover_string_concat_char_func)
    res=add_axioms_for_concat_char(expr);
  else if(id==ID_cprover_string_concat_double_func)
    res=add_axioms_for_concat_double(expr);
  else if(id==ID_cprover_string_concat_float_func)
    res=add_axioms_for_concat_float(expr);
  else if(id==ID_cprover_string_concat_code_point_func)
    res=add_axioms_for_concat_code_point(expr);
  else if(id==ID_cprover_string_insert_func)
    res=add_axioms_for_insert(expr);
  else if(id==ID_cprover_string_insert_int_func)
    res=add_axioms_for_insert_int(expr);
  else if(id==ID_cprover_string_insert_long_func)
    res=add_axioms_for_insert_long(expr);
  else if(id==ID_cprover_string_insert_bool_func)
    res=add_axioms_for_insert_bool(expr);
  else if(id==ID_cprover_string_insert_char_func)
    res=add_axioms_for_insert_char(expr);
  else if(id==ID_cprover_string_insert_double_func)
    res=add_axioms_for_insert_double(expr);
  else if(id==ID_cprover_string_insert_float_func)
    res=add_axioms_for_insert_float(expr);
#if 0
  else if(id==ID_cprover_string_insert_char_array_func)
    res=add_axioms_for_insert_char_array(expr);
#endif
  else if(id==ID_cprover_string_substring_func)
    res=add_axioms_for_substring(expr);
  else if(id==ID_cprover_string_trim_func)
    res=add_axioms_for_trim(expr);
  else if(id==ID_cprover_string_to_lower_case_func)
    res=add_axioms_for_to_lower_case(expr);
  else if(id==ID_cprover_string_to_upper_case_func)
    res=add_axioms_for_to_upper_case(expr);
  else if(id==ID_cprover_string_char_set_func)
    res=add_axioms_for_char_set(expr);
  else if(id==ID_cprover_string_value_of_func)
    res=add_axioms_for_value_of(expr);
  else if(id==ID_cprover_string_empty_string_func)
    res=add_axioms_for_empty_string(expr);
  else if(id==ID_cprover_string_copy_func)
    res=add_axioms_for_copy(expr);
  else if(id==ID_cprover_string_of_int_func)
    res=add_axioms_from_int(expr);
  else if(id==ID_cprover_string_of_int_hex_func)
    res=add_axioms_from_int_hex(expr);
  else if(id==ID_cprover_string_of_float_func)
    res=add_axioms_from_float(expr);
  else if(id==ID_cprover_string_of_double_func)
    res=add_axioms_from_double(expr);
  else if(id==ID_cprover_string_of_long_func)
    res=add_axioms_from_long(expr);
  else if(id==ID_cprover_string_of_bool_func)
    res=add_axioms_from_bool(expr);
  else if(id==ID_cprover_string_of_char_func)
    res=add_axioms_from_char(expr);
  else if(id==ID_cprover_string_set_length_func)
    res=add_axioms_for_set_length(expr);
  else if(id==ID_cprover_string_delete_func)
    res=add_axioms_for_delete(expr);
  else if(id==ID_cprover_string_delete_char_at_func)
    res=add_axioms_for_delete_char_at(expr);
  else if(id==ID_cprover_string_replace_func)
    res=add_axioms_for_replace(expr);
  else if(id==ID_cprover_string_intern_func)
    res=add_axioms_for_intern(expr);
  else if(id==ID_cprover_string_array_of_char_pointer_func)
    res=add_axioms_for_char_pointer(expr);
  else
  {
    std::string msg(
      "string_constraint_generator::function_application: unknown symbol :");
    msg+=id2string(id);
    throw msg;
  }
  function_application_cache[expr]=res;
  return res;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_copy

  Inputs: function application with one argument, which is a string,
          or three arguments: string, integer offset and count

 Outputs: a new string expression

 Purpose: add axioms to say that the returned string expression is equal to
          the argument of the function application

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_copy(
  const function_application_exprt &f)
{
  const auto &args=f.arguments();
  if(args.size()==1)
  {
    string_exprt s1=get_string_expr(args[0]);
    return s1;
  }
  else
  {
    assert(args.size()==3);
    string_exprt s1=get_string_expr(args[0]);
    exprt offset=args[1];
    exprt count=args[2];
    return add_axioms_for_substring(s1, offset, plus_exprt(offset, count));
  }
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_java_char_array

  Inputs: an expression corresponding to a java object of type char array

 Outputs: a new string expression

 Purpose: add axioms corresponding to the String.valueOf([C) java function

\*******************************************************************/

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

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_char_pointer

  Inputs: an expression of type char

 Outputs: an array expression

 Purpose: for an expression of the form `array[0]` returns `array`

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_char_pointer(
  const function_application_exprt &fun)
{
  exprt char_pointer=args(fun, 1)[0];
  if(char_pointer.id()==ID_index)
    return char_pointer.op0();
  // TODO: we do not know what to do in the other cases
  assert(false);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_length

  Inputs: function application with one string argument

 Outputs: a string expression of index type

 Purpose: add axioms corresponding to the String.length java function

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_length(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 1)[0]);
  return str.length();
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_char_array

  Inputs: a length expression, an array expression, a offset index, and a
          count index

 Outputs: a new string expression

 Purpose: add axioms stating that the content of the returned string
          equals to the content of the array argument, starting at offset and
          with `count` characters

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_char_array(
  const exprt &length,
  const exprt &data,
  const exprt &offset,
  const exprt &count)
{
  assert(false); // deprecated, we should use add_axioms_for_substring instead
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
  char_in_tab.op1()=plus_exprt_with_overflow_check(qvar, offset);

  string_constraintt a1(qvar, count, equal_exprt(str[qvar], char_in_tab));
  axioms.push_back(a1);
  axioms.push_back(equal_exprt(str.length(), count));

  return str;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_char_array

  Inputs: function application with 2 arguments and 2 additional optional
          arguments: length, char array, offset and count

 Outputs: a new string expression

 Purpose: add axioms corresponding to the String.<init>:(I[CII)
          and String.<init>:(I[C) java functions

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_char_array(
  const function_application_exprt &f)
{
  assert(false); // deprecated, we should use add_axioms_for_substring instead
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

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_is_positive_index

  Inputs: an index expression

 Outputs: a Boolean expression

 Purpose: expression true exactly when the index is positive

\*******************************************************************/

exprt string_constraint_generatort::axiom_for_is_positive_index(const exprt &x)
{
  return binary_relation_exprt(
    x, ID_ge, from_integer(0, x.type()));
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_char_literal

  Inputs: function application with one character argument

 Outputs: a new character expression

 Purpose: add axioms stating that the returned value is equal to the argument

\*******************************************************************/

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

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_char_at

  Inputs: function application with two arguments: a string and an integer

 Outputs: a character expression

 Purpose: add axioms stating that the character of the string at the given
          position is equal to the returned value

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_char_at(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 2)[0]);
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  symbol_exprt char_sym=fresh_symbol("char", ref_type.get_char_type());
  axioms.push_back(equal_exprt(char_sym, str[args(f, 2)[1]]));
  return char_sym;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_to_char_array

  Inputs: function application with one string argument

 Outputs: a char array expression

 Purpose: add axioms corresponding to the String.toCharArray java function

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_to_char_array(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 1)[0]);
  return str.content();
}

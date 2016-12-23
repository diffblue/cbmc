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

/*******************************************************************\

Function: string_constraint_generatort::constant_char

  Inputs: integer representing a character, we do not use char type here
          because java characters use more than 8 bits.

 Outputs: constant expression corresponding to the character.

 Purpose: generate constant character expression with character type.

\*******************************************************************/

constant_exprt string_constraint_generatort::constant_char(int i) const
{
  return from_integer(i, get_char_type());
}

/*******************************************************************\

Function: string_constraint_generatort::get_char_type

 Outputs: a type for characters

 Purpose: returns the type of characters that is adapted to the current mode

\*******************************************************************/

typet string_constraint_generatort::get_char_type() const
{
  if(mode==ID_C)
    return char_type();
  else if(mode==ID_java)
    return java_char_type();
  else
    assert(false); // only C and java modes supported
}

/*******************************************************************\

Function: string_constraint_generatort::fresh_univ_index

  Inputs: a prefix

 Outputs: a symbol of index type whose name starts with the prefix

 Purpose: generate an index symbol to be used as an universaly quantified
          variable

\*******************************************************************/

symbol_exprt string_constraint_generatort::fresh_univ_index(
  const irep_idt &prefix)
{
  return string_exprt::fresh_symbol(prefix, get_index_type());
}

/*******************************************************************\

Function: string_constraint_generatort::fresh_exist_index

  Inputs: a prefix

 Outputs: a symbol of index type whose name starts with the prefix

 Purpose: generate an index symbol which is existentially quantified

\*******************************************************************/

symbol_exprt string_constraint_generatort::fresh_exist_index(
  const irep_idt &prefix)
{
  symbol_exprt s=string_exprt::fresh_symbol(prefix, get_index_type());
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
  symbol_exprt b=string_exprt::fresh_symbol(prefix, bool_typet());
  boolean_symbols.push_back(b);
  return b;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_string_expr

  Inputs: an expression of type string

 Outputs: a string expression that is linked to the argument through
          axioms that are added to the list

 Purpose: obtain a refined string expression corresponding to string
          variable of string function call

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_string_expr(
  const exprt &unrefined_string)
{
  string_exprt s;

  if(unrefined_string.id()==ID_function_application)
  {
    exprt res=add_axioms_for_function_application(
      to_function_application_expr(unrefined_string));
    assert(res.type()==refined_string_type);
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
    assert(res.type()==refined_string_typet(get_char_type()));
    s=to_string_expr(res);
  }
  else
  {
    throw "add_axioms_for_string_expr:\n"+unrefined_string.pretty()+
      "\nwhich is not a function application, "+
      "a symbol or an if expression";
  }

  axioms.push_back(
    s.axiom_for_is_longer_than(from_integer(0, get_index_type())));
  return s;
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
  string_exprt res(get_char_type());
  assert(
    refined_string_typet::is_unrefined_string_type(expr.true_case().type()));
  string_exprt t=add_axioms_for_string_expr(expr.true_case());
  assert(
    refined_string_typet::is_unrefined_string_type(expr.false_case().type()));
  string_exprt f=add_axioms_for_string_expr(expr.false_case());

  axioms.push_back(
    implies_exprt(expr.cond(), res.axiom_for_has_same_length_as(t)));
  symbol_exprt qvar=fresh_univ_index("QA_string_if_true");
  equal_exprt qequal(res[qvar], t[qvar]);
  axioms.push_back(string_constraintt(qvar, t.length(), expr.cond(), qequal));
  axioms.push_back(
    implies_exprt(not_exprt(expr.cond()), res.axiom_for_has_same_length_as(f)));
  symbol_exprt qvar2=fresh_univ_index("QA_string_if_false");
  equal_exprt qequal2(res[qvar2], f[qvar2]);
  string_constraintt sc2(qvar2, f.length(), not_exprt(expr.cond()), qequal2);
  axioms.push_back(sc2);
  return res;
}

/*******************************************************************\

Function: string_constraint_generatort::find_or_add_string_of_symbol

  Inputs: a symbol expression

 Outputs: a string expression

 Purpose: if a symbol represent a string is present in the symbol_to_string
          table, returns the corresponding string, if the symbol is not yet
          present, creates a new string with the correct type depending on
          whether the mode is java or c, adds it to the table and returns it.

\*******************************************************************/

string_exprt string_constraint_generatort::find_or_add_string_of_symbol(
  const symbol_exprt &sym)
{
  irep_idt id=sym.get_identifier();
  auto entry=symbol_to_string.insert(
    std::make_pair(id, string_exprt(get_char_type())));
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
  else if(id==ID_cprover_string_data_func)
    return add_axioms_for_data(expr);
  else
  {
    std::string msg("string_exprt::function_application: unknown symbol :");
    msg+=id2string(id);
    throw msg;
  }
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_copy

  Inputs: function application with one argument, which is a string

 Outputs: a new string expression

 Purpose: add axioms to say that the returned string expression is equal to
          the argument of the function application

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_copy(
  const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 1)[0]);
  string_exprt res(get_char_type());

  // We add axioms:
  // a1 : |res|=|s1|
  // a2 : forall i<|s1|. s1[i]=res[i]

  axioms.push_back(res.axiom_for_has_same_length_as(s1));

  symbol_exprt idx=fresh_univ_index("QA_index_copy");
  string_constraintt a2(idx, s1.length(), equal_exprt(s1[idx], res[idx]));
  axioms.push_back(a2);
  return res;
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
  string_exprt res(get_char_type());
  exprt arr=to_address_of_expr(char_array).object();
  exprt len=member_exprt(arr, "length", res.length().type());
  exprt cont=member_exprt(arr, "data", res.content().type());
  res.length()=len;
  res.content()=cont;
  return res;
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
  string_exprt str=add_axioms_for_string_expr(args(f, 1)[0]);
  return str.length();
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_data

  Inputs: function application with three arguments: one string, a java
          Array object and the corresponding data field

 Outputs: an expression of type void

 Purpose: add axioms stating that the content of the string argument is
          equal to the content of the array argument

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_data(
  const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 3)[0]);
  const exprt &tab_data=args(f, 3)[1];
  const exprt &data=args(f, 3)[2];
  symbol_exprt qvar=fresh_univ_index("QA_string_data");

  // translating data[qvar]  to the correct expression
  // which is (signed int)byte_extract_little_endian
  // (data, (2l*qvar) + POINTER_OFFSET(byte_extract_little_endian
  //  (tab.data, 0l, unsigned short int *)), unsigned short int)
  mult_exprt qvar2(
    from_integer(2, java_long_type()),
    typecast_exprt(qvar, java_long_type()));
  byte_extract_exprt extract(
    ID_byte_extract_little_endian,
    tab_data,
    from_integer(0, java_long_type()),
    pointer_typet(java_char_type()));
  plus_exprt arg2(qvar2, pointer_offset(extract));

  byte_extract_exprt extract2(
    ID_byte_extract_little_endian, data, arg2, java_char_type());
  exprt char_in_tab=typecast_exprt(extract2, get_char_type());

  string_constraintt eq(
    qvar, str.length(), equal_exprt(str[qvar], char_in_tab));
  axioms.push_back(eq);

  exprt void_expr;
  void_expr.type()=void_typet();
  return void_expr;
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
  string_exprt str(get_char_type());

  // We add axioms:
  // a1 : forall q < count. str[q] = data[q+offset]
  // a2 : |str| = count

  symbol_exprt qvar=fresh_univ_index("QA_string_of_char_array");
  exprt char_in_tab=data;
  assert(char_in_tab.id()==ID_index);
  char_in_tab.op1()=plus_exprt(qvar, offset);

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
    offset=from_integer(0, get_index_type());
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
    x, ID_ge, from_integer(0, get_index_type()));
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
    return from_integer(unsigned(sval[0]), get_char_type());
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
  string_exprt str=add_axioms_for_string_expr(args(f, 2)[0]);
  symbol_exprt char_sym=string_exprt::fresh_symbol("char", get_char_type());
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
  string_exprt str=add_axioms_for_string_expr(args(f, 1)[0]);
  return str.content();
}

/*******************************************************************\

Function: string_constraint_generatort::set_string_symbol_equal_to_expr

  Inputs: a symbol and a string

 Purpose: add a correspondence to make sure the symbol points to the
          same string as the second argument

\*******************************************************************/

void string_constraint_generatort::set_string_symbol_equal_to_expr(
  const symbol_exprt &sym, const exprt &str)
{
  if(str.id()==ID_symbol)
    assign_to_symbol(sym, find_or_add_string_of_symbol(to_symbol_expr(str)));
  else
    assign_to_symbol(sym, add_axioms_for_string_expr(str));
}

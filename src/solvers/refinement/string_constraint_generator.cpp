/** -*- C++ -*- *****************************************************\

Module: Constraint generation from string function calls
        for the PASS algorithm (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint_generator.h>
#include <util/unicode.h>
#include <ansi-c/string_constant.h>
#include <solvers/floatbv/float_bv.h>
#include <java_bytecode/java_types.h>
#include <util/pointer_predicates.h>
#include <util/arith_tools.h>
#include <util/prefix.h>
#include <util/ssa_expr.h>

constant_exprt string_constraint_generatort::constant_char(int i) const
{
  if(mode==ID_C)
    return from_integer(i, refined_string_typet::char_type());
  else if(mode==ID_java)
    return from_integer(i, refined_string_typet::java_char_type());
  else
    assert(false); // only C and java modes supported
}

unsignedbv_typet string_constraint_generatort::get_char_type() const
{
  if(mode==ID_C)
    return refined_string_typet::char_type();
  else if(mode==ID_java)
    return refined_string_typet::java_char_type();
  else
    assert(false); // only C and java modes supported
}

size_t string_constraint_generatort::get_char_width() const
{
  if(mode==ID_C)
    return STRING_SOLVER_C_CHAR_WIDTH;
  else if(mode==ID_java)
    return STRING_SOLVER_JAVA_CHAR_WIDTH;
  else
    assert(false); // only C and java modes supported
}

symbol_exprt string_constraint_generatort::fresh_univ_index
(const irep_idt &prefix)
{
  return string_exprt::fresh_symbol(prefix, refined_string_typet::index_type());
}

symbol_exprt string_constraint_generatort::fresh_exist_index
(const irep_idt &prefix)
{
  symbol_exprt s=string_exprt::fresh_symbol
    (prefix, refined_string_typet::index_type());
  index_symbols.push_back(s);
  return s;
}

symbol_exprt string_constraint_generatort::fresh_boolean
(const irep_idt &prefix)
{
  symbol_exprt b=string_exprt::fresh_symbol(prefix, bool_typet());
  boolean_symbols.push_back(b);
  return b;
}


string_exprt string_constraint_generatort::add_axioms_for_string_expr
(const exprt & unrefined_string)
{
  string_exprt s;

  if(unrefined_string.id()==ID_function_application)
  {
    exprt res=add_axioms_for_function_application
      (to_function_application_expr(unrefined_string));
    assert(res.type()==refined_string_typet(get_char_type()));
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
  else if(unrefined_string.id()==ID_nondet_symbol
          || unrefined_string.id()==ID_struct)
  {
    // We ignore non deterministic symbols and struct
  }
  else
  {
    throw("add_axioms_for_string_expr:\n"+unrefined_string.pretty()+
          "\nwhich is not a function application, "+
          "a symbol or an if expression");
  }

  axioms.push_back(s.longer(refined_string_typet::index_zero()));
  return s;
}

string_exprt string_constraint_generatort::add_axioms_for_if
(const if_exprt &expr)
{
  string_exprt res(get_char_type());
  assert(refined_string_typet::is_unrefined_string_type
    (expr.true_case().type()));
  string_exprt t=add_axioms_for_string_expr(expr.true_case());
  assert(refined_string_typet::is_unrefined_string_type
    (expr.false_case().type()));
  string_exprt f=add_axioms_for_string_expr(expr.false_case());

  axioms.push_back(implies_exprt(expr.cond(), res.same_length(t)));
  symbol_exprt qvar=fresh_univ_index("QA_string_if_true");
  equal_exprt qequal(res[qvar], t[qvar]);
  axioms.push_back(string_constraintt(qvar, t.length(), expr.cond(), qequal));
  axioms.push_back(implies_exprt(expr.cond(), res.same_length(f)));
  symbol_exprt qvar2=fresh_univ_index("QA_string_if_false");
  equal_exprt qequal2(res[qvar2], f[qvar2]);
  string_constraintt sc2(qvar2, f.length(), not_exprt(expr.cond()), qequal2);
  axioms.push_back(sc2);
  return res;
}


string_exprt string_constraint_generatort::find_or_add_string_of_symbol
(const symbol_exprt & sym)
{
  irep_idt id=sym.get_identifier();
  std::map<irep_idt, string_exprt>::iterator f=symbol_to_string.find(id);
  if(f!=symbol_to_string.end())
    return f->second;

  symbol_to_string[id]= string_exprt(get_char_type());
  return symbol_to_string[id];
}


exprt string_constraint_generatort::add_axioms_for_function_application
(const function_application_exprt & expr)
{
  const exprt &name=expr.function();
  assert(name.id()==ID_symbol);

  const irep_idt &id=is_ssa_expr(name)?to_ssa_expr(name).get_object_name():
    to_symbol_expr(name).get_identifier();

  if(id==ID_cprover_char_literal_func)
    return add_axioms_for_char_literal(expr);
  else if(id==ID_cprover_string_length_func)
    return add_axioms_for_length(expr);
  else if(id==ID_cprover_string_equal_func)
    return add_axioms_for_equal(expr);
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
    msg+=id.c_str();
    throw msg;
  }
}


irep_idt extract_java_string(const symbol_exprt & s)
{
  std::string tmp(s.get(ID_identifier).c_str());
  std::string prefix("java::java.lang.String.Literal.");
  assert(has_prefix(tmp, prefix));
  std::string value=tmp.substr(prefix.length());
  return irep_idt(value);
}

string_exprt string_constraint_generatort::add_axioms_for_constant
(irep_idt sval, int char_width, unsignedbv_typet char_type)
{
  string_exprt res(char_type);
  std::string str=sval.c_str();
  // should only do this for java
  std::wstring utf16=utf8_to_utf16le(str);

  for(std::size_t i=0; i<utf16.size(); i++)
  {
    exprt idx=from_integer(i, refined_string_typet::index_type());
    exprt c=from_integer((unsigned)utf16[i], char_type);
    equal_exprt lemma(res[idx], c);
    axioms.push_back(lemma);
  }

  exprt s_length=from_integer(unsigned(utf16.size()),
                              refined_string_typet::index_type());

  axioms.push_back(res.has_length(s_length));
  return res;
}

string_exprt string_constraint_generatort::add_axioms_for_constant
(irep_idt sval)
{
  return add_axioms_for_constant(sval, get_char_width(), get_char_type());
}

string_exprt string_constraint_generatort::add_axioms_for_empty_string
(const function_application_exprt &f)
{
  assert(f.arguments().size()==0);
  string_exprt res(get_char_type());
  axioms.push_back(res.has_length(0));
  return res;
}

string_exprt string_constraint_generatort::add_axioms_from_literal
(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(args.size()==1); // Bad args to string literal?

  const exprt &arg=args[0];

  irep_idt sval;
  int char_width;
  unsignedbv_typet char_type;
  if(arg.operands().size()==1 &&
      arg.op0().operands().size()==2 &&
      arg.op0().op0().id()==ID_string_constant)
  {
    // C string constant
    const exprt &s=arg.op0().op0();
    sval=to_string_constant(s).get_value();
    char_width=STRING_SOLVER_C_CHAR_WIDTH;
    char_type=refined_string_typet::char_type();
  }
  else
  {
    // Java string constant
    assert(arg.operands().size()==1);
    assert(refined_string_typet::is_unrefined_string_type(arg.type()));
    const exprt &s=arg.op0();

    // It seems the value of the string is lost,
    // we need to recover it from the identifier
    sval=extract_java_string(to_symbol_expr(s));
    char_width=STRING_SOLVER_JAVA_CHAR_WIDTH;
    char_type=refined_string_typet::java_char_type();
  }

  return add_axioms_for_constant(sval, char_width, char_type);
}


string_exprt string_constraint_generatort::add_axioms_for_concat
(const string_exprt & s1, const string_exprt & s2)
{
  // |res|=|s1| + |s2|
  string_exprt res(get_char_type());
  axioms.push_back(res.has_length(plus_exprt(s1.length(), s2.length())));
  // we have to be careful about very long strings:
  axioms.push_back(s1.shorter(res));
  axioms.push_back(s2.shorter(res));

  // forall i<|s1|. res[i]=s1[i]
  symbol_exprt idx=fresh_univ_index("QA_index_concat");
  string_constraintt a1(idx, s1.length(), equal_exprt(s1[idx], res[idx]));
  axioms.push_back(a1);

  // forall i<|s2|. res[i+|s1|]=s2[i]
  symbol_exprt idx2=fresh_univ_index("QA_index_concat2");
  equal_exprt res_eq(s2[idx2], res[plus_exprt(idx2, s1.length())]);
  string_constraintt a2(idx2, s2.length(), res_eq);
  axioms.push_back(a2);

  return res;
}


string_exprt string_constraint_generatort::add_axioms_for_concat
(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(args.size()==2);

  string_exprt s1=add_axioms_for_string_expr(args[0]);
  string_exprt s2=add_axioms_for_string_expr(args[1]);

  return add_axioms_for_concat(s1, s2);
}


string_exprt string_constraint_generatort::add_axioms_for_copy
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 1)[0]);
  string_exprt res(get_char_type());
  axioms.push_back(res.same_length(s1));
  symbol_exprt idx=fresh_univ_index("QA_index_copy");
  string_constraintt a1(idx, s1.length(), equal_exprt(s1[idx], res[idx]));
  axioms.push_back(a1);
  return res;
}

string_exprt string_constraint_generatort::add_axioms_for_set_length
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  exprt k=args(f, 2)[1];
  string_exprt res(get_char_type());

  // |s|=k
  // && forall i<k. (i<k ==> s[i]=s1[i]) && (i >= k ==> s[i]=0)

  axioms.push_back(res.has_length(k));
  symbol_exprt idx=fresh_univ_index("QA_index_set_length");
  string_constraintt a1
    (idx, k, and_exprt
      (implies_exprt(s1.strictly_longer(idx), equal_exprt(s1[idx], res[idx])),
       implies_exprt(s1.shorter(idx), equal_exprt(s1[idx], constant_char(0)))));
  axioms.push_back(a1);

  return res;
}


string_exprt string_constraint_generatort::add_axioms_for_java_char_array
(const exprt & char_array)
{
  string_exprt res(get_char_type());
  exprt arr=to_address_of_expr(char_array).object();
  exprt len=member_exprt(arr, "length", res.length().type());
  exprt cont=member_exprt(arr, "data", res.content().type());
  res.op0()=len;
  res.op1()=cont;
  return res;
}


string_exprt string_constraint_generatort::add_axioms_for_value_of
(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  if(args.size()==3)
    {
      string_exprt res(get_char_type());
      exprt char_array=args[0];
      exprt offset=args[1];
      exprt count=args[2];
      string_exprt str=add_axioms_for_java_char_array(char_array);
      axioms.push_back(res.has_length(count));
      symbol_exprt idx=fresh_univ_index("QA_index_value_of");
      equal_exprt eq(str[plus_exprt(idx, offset)], res[idx]);
      string_constraintt a1(idx, count, eq);
      axioms.push_back(a1);
      return res;
    }
  else
    {
      assert(args.size()==1);
      return add_axioms_for_java_char_array(args[0]);
    }
}

string_exprt string_constraint_generatort::add_axioms_for_substring
(const function_application_exprt &f)
{
  assert(f.arguments().size()>=2);
  string_exprt str=add_axioms_for_string_expr(f.arguments()[0]);
  exprt i(f.arguments()[1]);
  exprt j;
  if(f.arguments().size()==3)
  {
    j=f.arguments()[2];
  }
  else
  {
    assert(f.arguments().size()==2);
    j=str.length();
  }
  return add_axioms_for_substring(str, i, j);
}

string_exprt string_constraint_generatort::add_axioms_for_substring
(const string_exprt & str, const exprt & start, const exprt & end)
{
  symbol_exprt idx=fresh_exist_index("index_substring");
  assert(start.type()==refined_string_typet::index_type());
  assert(end.type()==refined_string_typet::index_type());
  string_exprt res(get_char_type());

  exprt is_empty=res.has_length(refined_string_typet::index_zero());
  axioms.push_back(implies_exprt(binary_relation_exprt(start, ID_lt, end),
                                 res.has_length(minus_exprt(end, start))));
  axioms.push_back(implies_exprt(binary_relation_exprt(start, ID_ge, end),
                                 is_empty));

  // Warning: check what to do if the string is not long enough
  axioms.push_back(str.longer(end));

  // forall idx<str.length, str[idx]=arg_str[idx+i]
  string_constraintt a(idx, res.length(),
                       equal_exprt(res[idx], str[plus_exprt(start, idx)]));
  axioms.push_back(a);
  return res;
}

string_exprt string_constraint_generatort::add_axioms_for_trim
(const function_application_exprt &expr)
{
  string_exprt str=add_axioms_for_string_expr(args(expr, 1)[0]);
  string_exprt res(get_char_type());
  symbol_exprt idx=fresh_exist_index("index_trim");
  exprt space_char=constant_char(' ');

  // We add axioms:
  // a1 : m + |s1| <= |str|
  // a2 : idx >= 0
  // a3 : str >= idx
  // a4 : |res|>= 0
  // a5 : |res|<=|str|
  //        (this is necessary to prevent exceeding the biggest integer)
  // a6 : forall n<m, str[n]=' '
  // a7 : forall n<|str|-m-|s1|, str[m+|s1|+n]=' '
  // a8 : forall n<|s1|, s[idx+n]=s1[n]
  // a9 : (s[m]!=' ' && s[m+|s1|-1]!=' ') || m=|s|
  //

  exprt a1=str.longer(plus_exprt(idx, res.length()));
  axioms.push_back(a1);

  binary_relation_exprt a2(idx, ID_ge, refined_string_typet::index_zero());
  axioms.push_back(a2);

  exprt a3=str.longer(idx);
  axioms.push_back(a3);

  exprt a4=res.longer(refined_string_typet::index_zero());
  axioms.push_back(a4);

  exprt a5=res.shorter(str);
  axioms.push_back(a5);

  symbol_exprt n=fresh_univ_index("QA_index_trim");
  string_constraintt a6(n, idx, equal_exprt(str[n], space_char));
  axioms.push_back(a6);

  symbol_exprt n2=fresh_univ_index("QA_index_trim2");
  minus_exprt bound(str.length(), plus_exprt(idx, res.length()));
  equal_exprt eqn2(str[plus_exprt(idx, plus_exprt(res.length(), n2))],
                   space_char);
  string_constraintt a7(n2, bound, eqn2);
  axioms.push_back(a7);

  symbol_exprt n3=fresh_univ_index("QA_index_trim3");
  equal_exprt eqn3(res[n3], str[plus_exprt(n3, idx)]);
  string_constraintt a8(n3, res.length(), eqn3);
  axioms.push_back(a8);

  equal_exprt space_before
    (str[minus_exprt(plus_exprt(idx, res.length()),
                     refined_string_typet::index_of_int(1))], space_char);
  or_exprt a9
    (equal_exprt(idx, str.length()),
     and_exprt(not_exprt(equal_exprt(str[idx], space_char)),
               not_exprt(space_before)));
  axioms.push_back(a9);
  return res;
}

string_exprt string_constraint_generatort::add_axioms_for_to_lower_case
(const function_application_exprt &expr)
{
  string_exprt str=add_axioms_for_string_expr(args(expr, 1)[0]);
  string_exprt res(get_char_type());
  exprt char_a=constant_char('a');
  exprt char_A=constant_char('A');
  exprt char_z=constant_char('z');
  exprt char_Z=constant_char('Z');

  // We add axioms:
  // a1 : |res| = |str|
  // a2 : forall idx<str.length, 'A'<=str[idx]<='Z' => res[idx]=str[idx]+'a'-'A'
  // a3 : forall idx<str.length, !('a'<=str[idx]<='z') => res[idx]=str[idx]
  // forall idx<str.length,
  // this[idx]='A'<=str[idx]<='Z' ? str[idx]+'a'-'A' : str[idx]

  exprt a1=res.same_length(str);
  axioms.push_back(a1);

  symbol_exprt idx=fresh_univ_index("QA_lower_case");
  exprt is_upper_case=and_exprt(binary_relation_exprt(char_A, ID_le, str[idx]),
                                binary_relation_exprt(str[idx], ID_le, char_Z));
  minus_exprt diff(char_a, char_A);
  equal_exprt convert(res[idx], plus_exprt(str[idx], diff));
  string_constraintt a2(idx, res.length(), is_upper_case, convert);
  axioms.push_back(a2);

  equal_exprt eq(res[idx], str[idx]);
  string_constraintt a3(idx, res.length(), not_exprt(is_upper_case), eq);
  axioms.push_back(a3);
  return res;
}


string_exprt string_constraint_generatort::add_axioms_for_to_upper_case
(const function_application_exprt &expr)
{
  string_exprt str=add_axioms_for_string_expr(args(expr, 1)[0]);
  string_exprt res(get_char_type());
  exprt char_a=constant_char('a');
  exprt char_A=constant_char('A');
  exprt char_z=constant_char('z');
  exprt char_Z=constant_char('Z');

  // We add axioms:
  // a1 : |res| = |str|
  // a2 : forall idx<str.length, 'a'<=str[idx]<='z' => res[idx]=str[idx]+'A'-'a'
  // a3 : forall idx<str.length, !('a'<=str[idx]<='z') => res[idx]=str[idx]
  exprt a1=res.same_length(str);
  axioms.push_back(a1);

  symbol_exprt idx=fresh_univ_index("QA_upper_case");
  exprt is_lower_case=and_exprt(binary_relation_exprt(char_a, ID_le, str[idx]),
                                binary_relation_exprt(str[idx], ID_le, char_z));
  minus_exprt diff(char_A, char_a);
  equal_exprt convert(res[idx], plus_exprt(str[idx], diff));
  string_constraintt a2(idx, res.length(), is_lower_case, convert);
  axioms.push_back(a2);

  equal_exprt eq(res[idx], str[idx]);
  string_constraintt a3(idx, res.length(), not_exprt(is_lower_case), eq);
  axioms.push_back(a3);
  return res;
}


string_exprt string_constraint_generatort::add_axioms_from_int
(const function_application_exprt &expr)
{ return add_axioms_from_int(args(expr, 1)[0], 10); }

string_exprt string_constraint_generatort::add_axioms_from_long
(const function_application_exprt &expr)
{ return add_axioms_from_int(args(expr, 1)[0], 30); }

string_exprt string_constraint_generatort::add_axioms_from_float
(const function_application_exprt &f)
{ return add_axioms_from_float(args(f, 1)[0], false); }

string_exprt string_constraint_generatort::add_axioms_from_double
(const function_application_exprt &f)
{ return add_axioms_from_float(args(f, 1)[0], true); }

string_exprt string_constraint_generatort::add_axioms_from_float
(const exprt &f, bool double_precision)
{
  // Warning: we currently only have partial specification
  unsignedbv_typet char_type=get_char_type();
  string_exprt res(char_type);
  axioms.push_back(res.shorter(refined_string_typet::index_of_int(24)));

  string_exprt magnitude(char_type);
  string_exprt sign_string(char_type);
  string_exprt nan_string=add_axioms_for_constant("NaN");

  // We add the axioms:
  // a1 : If the argument is NaN, the result length is that of "NaN".
  // a2 : If the argument is NaN, the result content is the string "NaN".
  // a3 : f<0 => |sign_string|=1
  // a4 : f>=0 => |sign_string|=0
  // a5 : f<0 => sign_string[0]='-'
  // a6 : f infinite => |magnitude|=|"Infinity"|
  // a7 : forall i<|"Infinity"|, f infinite => magnitude[i]="Infinity"[i]
  // a8 : f=0 => |magnitude|=|"0.0"|
  // a9 : forall i<|"0.0"|, f=0 => f[i]="0.0"[i]
  ieee_float_spect fspec=
    double_precision?ieee_float_spect::double_precision()
    :ieee_float_spect::single_precision();

  exprt isnan=float_bvt().isnan(f, fspec);
  implies_exprt a1(isnan, magnitude.same_length(nan_string));
  axioms.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_equal_nan");
  string_constraintt a2(qvar, nan_string.length(),
                        isnan, equal_exprt(magnitude[qvar], nan_string[qvar]));
  axioms.push_back(a2);

  // If the argument is not NaN, the result is a string that represents
  // the sign and magnitude (absolute value) of the argument.
  // If the sign is negative, the first character of the result is '-';
  // if the sign is positive, no sign character appears in the result.

  const bitvector_typet &bv_type=to_bitvector_type(f.type());
  unsigned width=bv_type.get_width();
  exprt isneg=extractbit_exprt(f, width-1);

  implies_exprt a3(isneg, sign_string.has_length(1));
  axioms.push_back(a3);

  implies_exprt a4(not_exprt(isneg), sign_string.has_length(0));
  axioms.push_back(a4);

  implies_exprt a5(isneg, equal_exprt(sign_string[0], constant_char('-')));
  axioms.push_back(a5);

  // If m is infinity, it is represented by the characters "Infinity";
  // thus, positive infinity produces the result "Infinity" and negative
  // infinity produces the result "-Infinity".

  string_exprt infinity_string=add_axioms_for_constant("Infinity");
  exprt isinf=float_bvt().isinf(f, fspec);
  implies_exprt a6(isinf, magnitude.same_length(infinity_string));
  axioms.push_back(a6);

  symbol_exprt qvar_inf=fresh_univ_index("QA_equal_infinity");
  equal_exprt meq(magnitude[qvar_inf], infinity_string[qvar_inf]);
  string_constraintt a7(qvar_inf, infinity_string.length(), isinf, meq);
  axioms.push_back(a7);

  // If m is zero, it is represented by the characters "0.0"; thus, negative
  // zero produces the result "-0.0" and positive zero produces "0.0".

  string_exprt zero_string=add_axioms_for_constant("0.0");
  exprt iszero=float_bvt().is_zero(f, fspec);
  implies_exprt a8(iszero, magnitude.same_length(zero_string));
  axioms.push_back(a8);

  symbol_exprt qvar_zero=fresh_univ_index("QA_equal_zero");
  equal_exprt eq_zero(magnitude[qvar_zero], zero_string[qvar_zero]);
  string_constraintt a9(qvar_zero, zero_string.length(), iszero, eq_zero);
  axioms.push_back(a9);

  return add_axioms_for_concat(sign_string, magnitude);
}


string_exprt string_constraint_generatort::add_axioms_from_bool
(const function_application_exprt &f)
{ return add_axioms_from_bool(args(f, 1)[0]); }


string_exprt string_constraint_generatort::add_axioms_from_bool(const exprt &i)
{
  unsignedbv_typet char_type=get_char_type();
  string_exprt res(char_type);

  assert(i.type()==bool_typet() || i.type().id()==ID_c_bool);

  typecast_exprt eq(i, bool_typet());

  string_exprt true_string=add_axioms_for_constant("true");
  string_exprt false_string=add_axioms_for_constant("false");

  axioms.push_back(implies_exprt(eq, res.same_length(true_string)));
  symbol_exprt qvar=fresh_univ_index("QA_equal_true");
  axioms.push_back
    (string_constraintt(qvar, true_string.length(), eq,
                        equal_exprt(res[qvar], true_string[qvar])));

  axioms.push_back(implies_exprt(not_exprt(eq), res.same_length(false_string)));
  symbol_exprt qvar1=fresh_univ_index("QA_equal_false");
  axioms.push_back
    (string_constraintt(qvar, false_string.length(), not_exprt(eq),
                        equal_exprt(res[qvar1], false_string[qvar1])));

  return res;
}

// Gives the smallest integer with `nb` digits
int smallest_by_digit(int nb)
{
  int res=1;
  for(int i=1; i<nb; i++)
    res*=10;
  return res;
}

string_exprt string_constraint_generatort::add_axioms_from_int
(const exprt &i, size_t max_size)
{
  string_exprt res(get_char_type());
  typet type=i.type();
  assert(type.id()==ID_signedbv);
  exprt ten=from_integer(10, type);
  exprt zero_char=constant_char('0');
  exprt nine_char=constant_char('9');
  exprt minus_char=constant_char('-');
  exprt zero=refined_string_typet::index_zero();
  exprt max=refined_string_typet::index_of_int(max_size);
  // We add axioms:
  // a1 : 0 <|res|<=max_size
  // a2 : (res[0]='-')||('0'<=res[0]<='9')

  and_exprt a1(res.strictly_longer(zero), res.shorter(max));
  axioms.push_back(a1);

  exprt chr=res[0];
  exprt starts_with_minus=equal_exprt(chr, minus_char);
  exprt starts_with_digit=and_exprt
    (binary_relation_exprt(chr, ID_ge, zero_char),
     binary_relation_exprt(chr, ID_le, nine_char));
  or_exprt a2(starts_with_digit, starts_with_minus);
  axioms.push_back(a2);

  for(size_t size=1; size<=max_size; size++)
  {
    // For each possible size, we add axioms:
    // all_numbers: forall 1<=i<=size. '0'<=res[i]<='9'
    // a3 : |res|=size&&'0'<=res[0]<='9' =>
    //      i=sum+str[0]-'0' && all_numbers
    // a4 : |res|=size&&res[0]='-' => i=-sum
    // a5 : size>1 => |res|=size&&'0'<=res[0]<='9' => res[0]!='0'
    // a6 : size>1 => |res|=size&&res[0]'-' => res[1]!='0'
    // a7 : size==max_size => i>1000000000
    exprt sum=from_integer(0, type);
    exprt all_numbers=true_exprt();
    chr=res[0];
    exprt first_value=typecast_exprt(minus_exprt(chr, zero_char), type);

    for(size_t j=1; j<size; j++)
    {
      chr=res[j];
      sum=plus_exprt(mult_exprt(sum, ten),
                     typecast_exprt(minus_exprt(chr, zero_char), type));
      first_value=mult_exprt(first_value, ten);
      and_exprt is_number(binary_relation_exprt(chr, ID_ge, zero_char),
                          binary_relation_exprt(chr, ID_le, nine_char));
      all_numbers=and_exprt(all_numbers, is_number);
    }

    axioms.push_back(all_numbers);

    equal_exprt premise=res.has_length(size);
    equal_exprt constr3(i, plus_exprt(sum, first_value));
    implies_exprt a3(and_exprt(premise, starts_with_digit), constr3);
    axioms.push_back(a3);

    implies_exprt a4(and_exprt(premise, starts_with_minus),
                     equal_exprt(i, unary_minus_exprt(sum)));
    axioms.push_back(a4);

    // disallow 0s at the beggining
    if(size>1)
    {
      equal_exprt r0_zero(res[zero], zero_char);
      implies_exprt a5(and_exprt(premise, starts_with_digit),
                       not_exprt(r0_zero));
      axioms.push_back(a5);

      exprt one=refined_string_typet::index_of_int(1);
      equal_exprt r1_zero(res[one], zero_char);
      implies_exprt a6(and_exprt(premise, starts_with_minus),
                       not_exprt(r1_zero));
      axioms.push_back(a6);
    }

    // we have to be careful when exceeding the maximal size of integers
    // Warning this should be different depending on max size
    if(size==max_size)
    {
      exprt smallest_with_10_digits=
        from_integer(smallest_by_digit(max_size), type);
      binary_relation_exprt big(i, ID_ge, smallest_with_10_digits);
      implies_exprt a7(premise, big);
      axioms.push_back(a7);
    }
  }
  return res;
}


exprt string_constraint_generatort::int_of_hex_char
(exprt chr, unsigned char_width, typet char_type) const
{
  exprt zero_char=constant_char('0');
  exprt nine_char=constant_char('9');
  exprt a_char=constant_char('a');
  return if_exprt(binary_relation_exprt(chr, ID_gt, nine_char),
                  minus_exprt(chr, constant_char(0x61-10)),
                  minus_exprt(chr, zero_char));
}


string_exprt string_constraint_generatort::add_axioms_from_int_hex
(const exprt &i)
{
  string_exprt res(get_char_type());
  typet type=i.type();
  assert(type.id()==ID_signedbv);
  exprt sixteen=from_integer(16, type);
  exprt minus_char=constant_char('-');
  exprt zero_char=constant_char('0');
  exprt nine_char=constant_char('9');
  exprt a_char=constant_char('a');
  exprt f_char=constant_char('f');

  size_t max_size=8;
  axioms.push_back(and_exprt(res.strictly_longer(0),
                             res.shorter(max_size)));

  for(size_t size=1; size<=max_size; size++)
  {
    exprt sum=from_integer(0, type);
    exprt all_numbers=true_exprt();
    exprt chr=res[0];

    for(size_t j=0; j<size; j++)
    {
      chr=res[j];
      exprt i=int_of_hex_char(chr, get_char_width(), get_char_type());
      sum=plus_exprt(mult_exprt(sum, sixteen), typecast_exprt(i, type));
      or_exprt is_number
        (and_exprt(binary_relation_exprt(chr, ID_ge, zero_char),
                   binary_relation_exprt(chr, ID_le, nine_char)),
         and_exprt(binary_relation_exprt(chr, ID_ge, a_char),
                   binary_relation_exprt(chr, ID_le, f_char)));
      all_numbers=and_exprt(all_numbers, is_number);
    }

    equal_exprt premise(res.has_length(size));
    axioms.push_back
      (implies_exprt(premise, and_exprt(equal_exprt(i, sum), all_numbers)));

    // disallow 0s at the beggining
    if(size>1)
      axioms.push_back
        (implies_exprt(premise, not_exprt(equal_exprt(res[0], zero_char))));
  }
  return res;
}

string_exprt string_constraint_generatort::add_axioms_from_int_hex
(const function_application_exprt &f)
{ return add_axioms_from_int_hex(args(f, 1)[0]); }

string_exprt string_constraint_generatort::add_axioms_from_char
(const function_application_exprt &f)
{ return add_axioms_from_char(args(f, 1)[0]); }

string_exprt string_constraint_generatort::add_axioms_from_char(const exprt &c)
{
  string_exprt res(get_char_type());
  and_exprt lemma(equal_exprt(res[0], c), res.has_length(1));
  axioms.push_back(lemma);
  return res;
}


string_exprt string_constraint_generatort::add_axioms_for_code_point
(const exprt &code_point)
{
  string_exprt res(get_char_type());
  typet type=code_point.type();
  assert(type.id()==ID_signedbv);

  // We add axioms:
  // a1 : code_point<0x010000 => |res|=1
  // a2 : code_point>=0x010000 => |res|=2
  // a3 : code_point<0x010000 => res[0]=code_point
  // a4 : code_point>=0x010000 => res[0]=0xD800+(code_point-0x10000)/0x0400
  // a5 : code_point>=0x010000 => res[1]=0xDC00+(code_point-0x10000)/0x0400
  // For more explenations about this conversion, see:
  //   https://en.wikipedia.org/wiki/UTF-16

  exprt hex010000=from_integer(0x010000, type);
  exprt hexD800=from_integer(0xD800, type);
  exprt hexDC00=from_integer(0xDC00, type);
  exprt hex0400=from_integer(0x0400, type);

  binary_relation_exprt small(code_point, ID_lt, hex010000);
  implies_exprt a1(small, res.has_length(1));
  axioms.push_back(a1);

  implies_exprt a2(not_exprt(small), res.has_length(2));
  axioms.push_back(a2);

  typecast_exprt code_point_as_char(code_point, get_char_type());
  implies_exprt a3(small, equal_exprt(res[0], code_point_as_char));
  axioms.push_back(a3);

  plus_exprt first_char
    (hexD800, div_exprt(minus_exprt(code_point, hex010000), hex0400));
  implies_exprt a4
    (not_exprt(small),
     equal_exprt(res[0], typecast_exprt(first_char, get_char_type())));
  axioms.push_back(a4);

  plus_exprt second_char(hexDC00, mod_exprt(code_point, hex0400));
  implies_exprt a5
     (not_exprt(small),
      equal_exprt(res[1], typecast_exprt(second_char, get_char_type())));
  axioms.push_back(a5);

  return res;
}


string_exprt string_constraint_generatort::add_axioms_for_char_set
(const function_application_exprt &f)
{
  string_exprt res(get_char_type());
  string_exprt str=add_axioms_for_string_expr(args(f, 3)[0]);
  with_exprt sarrnew(str.content(), args(f, 3)[1], args(f, 3)[2]);
  implies_exprt lemma(binary_relation_exprt(args(f, 3)[1], ID_lt, str.length()),
                      and_exprt(equal_exprt(res.content(), sarrnew),
                                res.same_length(str)));
  axioms.push_back(lemma);
  return res;
}

string_exprt string_constraint_generatort::add_axioms_for_replace
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 3)[0]);
  exprt oldChar=args(f, 3)[1];
  exprt newChar=args(f, 3)[2];
  string_exprt res(get_char_type());

  // We add axioms:
  // a1 : |res| = |str|
  // a2 : forall qvar, 0<=qvar<|res|,
  //    str[qvar]=oldChar => res[qvar]=newChar
  //    !str[qvar]=oldChar => res[qvar]=str[qvar]

  axioms.push_back(res.same_length(str));

  symbol_exprt qvar=fresh_univ_index("QA_replace");
  implies_exprt case1(equal_exprt(str[qvar], oldChar),
                      equal_exprt(res[qvar], newChar));
  implies_exprt case2(not_exprt(equal_exprt(str[qvar], oldChar)),
                      equal_exprt(res[qvar], str[qvar]));
  string_constraintt a1(qvar, res.length(), and_exprt(case1, case2));
  axioms.push_back(a1);
  return res;
}

string_exprt string_constraint_generatort::add_axioms_for_delete_char_at
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 2)[0]);
  exprt index_one=refined_string_typet::index_of_int(1);
  return add_axioms_for_delete(str, args(f, 2)[1],
                               plus_exprt(args(f, 2)[1], index_one));
}

string_exprt string_constraint_generatort::add_axioms_for_delete
(const string_exprt &str, const exprt & start, const exprt & end)
{
  assert(start.type()==refined_string_typet::index_type());
  assert(end.type()==refined_string_typet::index_type());
  string_exprt str1=add_axioms_for_substring
    (str, refined_string_typet::index_zero(), start);
  string_exprt str2=add_axioms_for_substring(str, end, str.length());
  return add_axioms_for_concat(str1, str2);
}

string_exprt string_constraint_generatort::add_axioms_for_delete
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 3)[0]);
  return add_axioms_for_delete(str, args(f, 3)[1], args(f, 3)[2]);
}


string_exprt string_constraint_generatort::add_axioms_for_concat_int
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_from_int(args(f, 2)[1], 10);
  return add_axioms_for_concat(s1, s2);
}

string_exprt string_constraint_generatort::add_axioms_for_concat_long
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_from_int(args(f, 2)[1], 30);
  return add_axioms_for_concat(s1, s2);
}

string_exprt string_constraint_generatort::add_axioms_for_concat_bool
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_from_bool(args(f, 2)[1]);
  return add_axioms_for_concat(s1, s2);
}

string_exprt string_constraint_generatort::add_axioms_for_concat_char
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_from_char(args(f, 2)[1]);
  return add_axioms_for_concat(s1, s2);
}

string_exprt string_constraint_generatort::add_axioms_for_concat_double
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_from_float(args(f, 2)[1], 30);
  return add_axioms_for_concat(s1, s2);
}

string_exprt string_constraint_generatort::add_axioms_for_concat_float
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_from_float(args(f, 2)[1], 10);
  return add_axioms_for_concat(s1, s2);
}

string_exprt string_constraint_generatort::add_axioms_for_concat_code_point
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_for_code_point(args(f, 2)[1]);
  return add_axioms_for_concat(s1, s2);
}

string_exprt string_constraint_generatort::add_axioms_for_insert
(const string_exprt & s1, const string_exprt & s2, const exprt & offset)
{
  assert(offset.type()==refined_string_typet::index_type());
  string_exprt pref=add_axioms_for_substring
    (s1, refined_string_typet::index_zero(), offset);
  string_exprt suf=add_axioms_for_substring(s1, offset, s1.length());
  string_exprt concat1=add_axioms_for_concat(pref, s2);
  return add_axioms_for_concat(concat1, suf);
}

string_exprt string_constraint_generatort::add_axioms_for_insert
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_for_string_expr(args(f, 3)[2]);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

string_exprt string_constraint_generatort::add_axioms_for_insert_int
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_int(args(f, 3)[2], 10);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

string_exprt string_constraint_generatort::add_axioms_for_insert_long
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_int(args(f, 3)[2], 30);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

string_exprt string_constraint_generatort::add_axioms_for_insert_bool
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_bool(args(f, 3)[2]);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

string_exprt string_constraint_generatort::add_axioms_for_insert_char
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_char(args(f, 3)[2]);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

string_exprt string_constraint_generatort::add_axioms_for_insert_double
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_float(args(f, 3)[2]);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}

string_exprt string_constraint_generatort::add_axioms_for_insert_float
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 3)[0]);
  string_exprt s2=add_axioms_from_float(args(f, 3)[2]);
  return add_axioms_for_insert(s1, s2, args(f, 3)[1]);
}


exprt string_constraint_generatort::add_axioms_for_equal
(const function_application_exprt &f)
{
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  symbol_exprt eq=fresh_boolean("equal");
  typecast_exprt tc_eq(eq, f.type());

  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_for_string_expr(args(f, 2)[1]);

  // We want to write:
  // eq <=> (s1.length=s2.length  && forall i<s1.length. s1[i]=s2[i])
  // We add axioms:
  // a1 : eq => s1.length=s2.length
  // a2 : forall i<s1.length. eq => s1[i]=s2[i]
  // a3 : !eq => s1.length!=s2.length
  //       || (witness<s1.length && s1[witness]!=s2[witness])

  implies_exprt a1(eq, s1.same_length(s2));
  axioms.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_equal");
  string_constraintt a2(qvar, s1.length(), eq, equal_exprt(s1[qvar], s2[qvar]));
  axioms.push_back(a2);

  symbol_exprt witness=fresh_exist_index("witness_unequal");
  exprt zero=refined_string_typet::index_zero();
  and_exprt bound_witness(binary_relation_exprt(witness, ID_lt, s1.length()),
                          binary_relation_exprt(witness, ID_ge, zero));
  and_exprt witnessing(bound_witness, notequal_exprt(s1[witness], s2[witness]));
  implies_exprt a3(not_exprt(eq),
                   or_exprt(notequal_exprt(s1.length(), s2.length()),
                            witnessing));
  axioms.push_back(a3);

  return tc_eq;
}

exprt character_equals_ignore_case
(exprt char1, exprt char2, exprt char_a, exprt char_A, exprt char_Z)
{
  exprt is_upper_case_1=and_exprt(binary_relation_exprt(char_A, ID_le, char1),
                                  binary_relation_exprt(char1, ID_le, char_Z));
  exprt is_upper_case_2=and_exprt(binary_relation_exprt(char_A, ID_le, char2),
                                  binary_relation_exprt(char2, ID_le, char_Z));

  // Three possibilities:
  // p1 : char1=char2
  // p2 : (is_up1&&'a'-'A'+char1=char2)
  // p3 : (is_up2&&'a'-'A'+char2=char1)
  equal_exprt p1(char1, char2);
  minus_exprt diff=minus_exprt(char_a, char_A);
  and_exprt p2(is_upper_case_1, equal_exprt(plus_exprt(diff, char1), char2));
  and_exprt p3(is_upper_case_2, equal_exprt(plus_exprt(diff, char2), char1));
  return or_exprt(or_exprt(p1, p2), p3);
}

exprt string_constraint_generatort::add_axioms_for_equals_ignore_case
(const function_application_exprt &f)
{
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);

  symbol_exprt eq=fresh_boolean("equal_ignore_case");
  typecast_exprt tc_eq(eq, f.type());
  exprt char_a=constant_char('a');
  exprt char_A=constant_char('A');
  exprt char_Z=constant_char('Z');
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_for_string_expr(args(f, 2)[1]);

  // We add axioms:
  // a1 : eq => |s1|=|s2|
  // a2 : forall qvar, 0<=qvar<|s1|,
  //  eq => char_equal_ignore_case(s1[qvar],s2[qvar]);
  // a3 : !eq => |s1|!=s2 || (0 <=witness<|s1| && !char_equal_ignore_case)

  implies_exprt a1(eq, s1.same_length(s2));
  axioms.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_equal_ignore_case");
  exprt constr2=
    character_equals_ignore_case(s1[qvar], s2[qvar], char_a, char_A, char_Z);
  string_constraintt a2(qvar, s1.length(), eq, constr2);
  axioms.push_back(a2);

  symbol_exprt witness=fresh_exist_index("witness_unequal_ignore_case");
  exprt zero=refined_string_typet::index_zero();
  and_exprt bound_witness
    (binary_relation_exprt(witness, ID_lt, s1.length()),
     binary_relation_exprt(witness, ID_ge, zero));
  exprt witness_eq=character_equals_ignore_case
    (s1[witness], s2[witness], char_a, char_A, char_Z);
  not_exprt witness_diff(witness_eq);
  implies_exprt a3(not_exprt(eq),
                   or_exprt(notequal_exprt(s1.length(), s2.length()),
                            and_exprt(bound_witness, witness_diff)));
  axioms.push_back(a3);

  return tc_eq;
}


exprt string_constraint_generatort::add_axioms_for_length
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 1)[0]);
  return str.length();
}

exprt string_constraint_generatort::add_axioms_for_data
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 3)[0]);
  exprt tab_data=args(f, 3)[1];
  exprt data=args(f, 3)[2];
  symbol_exprt qvar=fresh_univ_index("QA_string_data");

  // translating data[qvar]  to the correct expression
  // which is (signed int)byte_extract_little_endian
  // (data, (2l*qvar) + POINTER_OFFSET(byte_extract_little_endian
  //  (tab.data, 0l, unsigned short int *)), unsigned short int)
  mult_exprt qvar2(from_integer(2, signedbv_typet(64)),
                   typecast_exprt(qvar, signedbv_typet(64)));
  byte_extract_exprt extract(
    ID_byte_extract_little_endian,
    tab_data,
    from_integer(0, signedbv_typet(64)),
    pointer_typet(unsignedbv_typet(16)));
  plus_exprt arg2(qvar2, pointer_offset(extract));

  byte_extract_exprt extract2
    (ID_byte_extract_little_endian, data, arg2, unsignedbv_typet(16));
  exprt char_in_tab= typecast_exprt(extract2, get_char_type());

  string_constraintt eq
    (qvar, str.length(), equal_exprt(str[qvar], char_in_tab));
  axioms.push_back(eq);

  exprt void_expr;
  void_expr.type()=void_typet();
  return void_expr;
}

string_exprt string_constraint_generatort::add_axioms_from_char_array(
  const exprt & length,
  const exprt & data,
  const exprt & offset,
  const exprt & count)
{
  string_exprt str(get_char_type());
  symbol_exprt qvar=fresh_univ_index("QA_string_of_char_array");
  exprt char_in_tab=data;
  assert(char_in_tab.id()==ID_index);
  char_in_tab.op1()=plus_exprt(qvar, offset);

  string_constraintt eq(qvar, count, equal_exprt(str[qvar], char_in_tab));
  axioms.push_back(eq);
  axioms.push_back(equal_exprt(str.length(), count));

  return str;
}

string_exprt string_constraint_generatort::add_axioms_from_char_array
(const function_application_exprt &f)
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
    offset=from_integer(0, signedbv_typet(32));
  }
  exprt tab_length=f.arguments()[0];
  exprt data=f.arguments()[1];
  return add_axioms_from_char_array(tab_length, data, offset, count);
}

string_exprt string_constraint_generatort::add_axioms_for_insert_char_array
(const function_application_exprt &f)
{
  exprt offset;
  exprt count;
  if(f.arguments().size()==6)
  {
    offset=f.arguments()[4];
    count=f.arguments()[5];
  }
  else
  {
    assert(f.arguments().size()==4);
    count=f.arguments()[2];
    offset=from_integer(0, signedbv_typet(32));
  }

  string_exprt str=add_axioms_for_string_expr(f.arguments()[0]);
  exprt length=f.arguments()[2];
  exprt data=f.arguments()[3];
  string_exprt arr=add_axioms_from_char_array(length, data, offset, count);
  return add_axioms_for_insert(str, arr, f.arguments()[1]);
}



exprt is_positive(const exprt & x)
{
  return binary_relation_exprt
    (x, ID_ge, refined_string_typet::index_of_int(0));
}


exprt string_constraint_generatort::add_axioms_for_is_prefix
  (const string_exprt &prefix, const string_exprt &str, const exprt & offset)
{
  symbol_exprt isprefix=fresh_boolean("isprefix");

  // We add axioms:
  // a1 : isprefix => |str| >= |prefix|+offset
  // a2 : forall 0<=qvar<prefix.length. isprefix =>
  //   s0[witness+offset]=s2[witness]
  // a3 : !isprefix => |str| < |prefix|+offset
  //   || (|str| >= |prefix|+offset && 0<=witness<|prefix|
  //     && str[witness+ofsset]!=prefix[witness])
  implies_exprt a1(isprefix, str.longer(plus_exprt(prefix.length(), offset)));
  axioms.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_isprefix");
  string_constraintt a2
    (qvar, prefix.length(), isprefix,
     equal_exprt(str[plus_exprt(qvar, offset)], prefix[qvar]));
  axioms.push_back(a2);

  symbol_exprt witness=fresh_exist_index("witness_not_isprefix");
  and_exprt witness_diff
    (is_positive(witness),
     and_exprt(prefix.strictly_longer(witness),
               notequal_exprt(str[plus_exprt(witness, offset)],
                              prefix[witness])));
  or_exprt s0_notpref_s1
    (not_exprt(str.longer(plus_exprt(prefix.length(), offset))),
     and_exprt(str.longer(plus_exprt(prefix.length(), offset)), witness_diff));

  implies_exprt a3(not_exprt(isprefix), s0_notpref_s1);
  axioms.push_back(a3);
  return isprefix;
}

exprt string_constraint_generatort::add_axioms_for_is_prefix
(const function_application_exprt &f, bool swap_arguments)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  string_exprt s0=add_axioms_for_string_expr(args[swap_arguments?1:0]);
  string_exprt s1=add_axioms_for_string_expr(args[swap_arguments?0:1]);
  exprt offset;
  if(args.size()==2)
    offset=refined_string_typet::index_zero();
  else if(args.size()==3)
    offset=args[2];
  return typecast_exprt(add_axioms_for_is_prefix(s0, s1, offset), f.type());
}

exprt string_constraint_generatort::add_axioms_for_is_empty
(const function_application_exprt &f)
{
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  symbol_exprt is_empty=fresh_boolean("is_empty");
  string_exprt s0=add_axioms_for_string_expr(args(f, 1)[0]);
  axioms.push_back(implies_exprt(is_empty, s0.has_length(0)));
  axioms.push_back(implies_exprt(s0.has_length(0), is_empty));
  return typecast_exprt(is_empty, f.type());
}

exprt string_constraint_generatort::add_axioms_for_is_suffix
(const function_application_exprt &f, bool swap_arguments)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(args.size()==2); // bad args to string issuffix?
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);

  symbol_exprt issuffix=fresh_boolean("issuffix");
  typecast_exprt tc_issuffix(issuffix, f.type());
  string_exprt s0=add_axioms_for_string_expr(args[swap_arguments?1:0]);
  string_exprt s1=add_axioms_for_string_expr(args[swap_arguments?0:1]);

  // We add axioms:
  // a1 : issufix => s0.length >= s1.length
  // a2 : forall witness<s1.length.
  //     issufix => s1[witness]=s0[witness + s0.length-s1.length]
  // a3 : !issuffix =>
  //   s1.length > s0.length
  //     || (s1.length > witness>=0
  //       && s1[witness]!=s0[witness + s0.length-s1.length]

  implies_exprt a1(issuffix, s1.longer(s0));
  axioms.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_suffix");
  exprt qvar_shifted=plus_exprt(qvar, minus_exprt(s1.length(), s0.length()));
  string_constraintt a2(qvar, s0.length(), issuffix,
                        equal_exprt(s0[qvar], s1[qvar_shifted]));
  axioms.push_back(a2);

  symbol_exprt witness=fresh_exist_index("witness_not_suffix");
  exprt shifted=plus_exprt(witness, minus_exprt(s1.length(), s0.length()));
  or_exprt constr3(s0.strictly_longer(s1),
                   and_exprt(notequal_exprt(s0[witness], s1[shifted]),
                             and_exprt(s0.strictly_longer(witness),
                                       is_positive(witness))));
  implies_exprt a3(not_exprt(issuffix), constr3);

  axioms.push_back(a3);

  return tc_issuffix;
}


exprt string_constraint_generatort::add_axioms_for_contains
(const function_application_exprt &f)
{
  assert(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  symbol_exprt contains=fresh_boolean("contains");
  typecast_exprt tc_contains(contains, f.type());
  string_exprt s0=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[1]);

  // We add axioms:
  // a1 : contains => s0.length >= s1.length
  // a2 : 0 <= startpos <= s0.length-s1.length
  // a3 : forall qvar<s1.length. contains => s1[qvar]=s0[startpos + qvar]
  // a4 : !contains => s1.length > s0.length
  //       || (forall startpos <= s0.length-s1.length.
  //             exists witness<s1.length && s1[witness]!=s0[witness + startpos]

  implies_exprt a1(contains, s0.longer(s1));
  axioms.push_back(a1);

  symbol_exprt startpos=fresh_exist_index("startpos_contains");
  minus_exprt length_diff(s0.length(), s1.length());
  and_exprt a2(is_positive(startpos),
               binary_relation_exprt(startpos, ID_le, length_diff));
  axioms.push_back(a2);

  symbol_exprt qvar=fresh_univ_index("QA_contains");
  exprt qvar_shifted=plus_exprt(qvar, startpos);
  string_constraintt a3(qvar, s1.length(), contains,
                        equal_exprt(s1[qvar], s0[qvar_shifted]));
  axioms.push_back(a3);

  // We rewrite the axiom for !contains as:
  // forall startpos <= |s0|-|s1|.  (!contains && |s0| >= |s1| )
  //      ==> exists witness<|s1|. s1[witness]!=s0[startpos+witness]
  string_not_contains_constraintt a4
    (refined_string_typet::index_zero(),
     plus_exprt(refined_string_typet::index_of_int(1), length_diff),
     and_exprt(not_exprt(contains), s0.longer(s1)),
     refined_string_typet::index_zero(), s1.length(), s0, s1);
  axioms.push_back(a4);

  return tc_contains;
}


exprt string_constraint_generatort::add_axioms_for_hash_code
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 1)[0]);
  typet return_type=f.type();

  // initialisation of the missing pool variable
  std::map<irep_idt, string_exprt>::iterator it;
  for(it=symbol_to_string.begin(); it!=symbol_to_string.end(); it++)
    if(hash.find(it->second)==hash.end())
      hash[it->second]=string_exprt::fresh_symbol("hash", return_type);

  // for each string s. either:
  //   c1: hash(str)=hash(s)
  //   c2: |str|!=|s|
  //   c3: (|str|==|s| && exists i<|s|. s[i]!=str[i])

  // WARNING: the specification may be incomplete
  for(it=symbol_to_string.begin(); it!=symbol_to_string.end(); it++)
  {
    symbol_exprt i=fresh_exist_index("index_hash");
    equal_exprt c1(hash[it->second], hash[str]);
    not_exprt c2(equal_exprt(it->second.length(), str.length()));
    and_exprt c3(equal_exprt(it->second.length(), str.length()),
                 and_exprt(not_exprt(equal_exprt(str[i], it->second[i])),
                           and_exprt(str.strictly_longer(i), is_positive(i))));
    axioms.push_back(or_exprt(c1, or_exprt(c2, c3)));
  }
  return hash[str];
}

exprt string_constraint_generatort::add_axioms_for_index_of
(const string_exprt &str, const exprt & c, const exprt & from_index)
{
  symbol_exprt index=fresh_exist_index("index_of");
  symbol_exprt contains=fresh_boolean("contains_in_index_of");

  // We add axioms:
  // a1 : -1 <= index<|str|
  // a2 : !contains <=> index=-1
  // a3 : contains => from_index<=index&&str[index]=c
  // a4 : forall n, from_index<=n<index. contains => str[n]!=c
  // a5 : forall m, from_index<=n<|str|. !contains => str[m]!=c

  exprt minus1=refined_string_typet::index_of_int(-1);
  and_exprt a1(binary_relation_exprt(index, ID_ge, minus1),
               binary_relation_exprt(index, ID_lt, str.length()));
  axioms.push_back(a1);

  equal_exprt a2(not_exprt(contains), equal_exprt(index, minus1));
  axioms.push_back(a2);

  implies_exprt a3
    (contains, and_exprt(binary_relation_exprt(from_index, ID_le, index),
                         equal_exprt(str[index], c)));
  axioms.push_back(a3);

  symbol_exprt n=fresh_univ_index("QA_index_of");
  string_constraintt a4
    (n, from_index, index, contains, not_exprt(equal_exprt(str[n], c)));
  axioms.push_back(a4);

  symbol_exprt m=fresh_univ_index("QA_index_of");
  string_constraintt a5(m, from_index, str.length(), not_exprt(contains),
                        not_exprt(equal_exprt(str[m], c)));
  axioms.push_back(a5);

  return index;
}

exprt string_constraint_generatort::add_axioms_for_index_of_string(
  const string_exprt &str,
  const string_exprt & substring,
  const exprt & from_index)
{
  symbol_exprt offset=fresh_exist_index("index_of");
  symbol_exprt contains=fresh_boolean("contains_substring");

  // We add axioms:
  // a1 : contains => |substring|>=offset>=from_index
  // a2 : !contains => offset=-1
  // a3 : forall 0 <= witness<substring.length.
  //   contains => str[witness+offset]=substring[witness]

  implies_exprt a1
    (contains, and_exprt(str.longer(plus_exprt(substring.length(), offset)),
                        binary_relation_exprt(offset, ID_ge, from_index)));
  axioms.push_back(a1);

  implies_exprt a2(not_exprt(contains),
                   equal_exprt(offset, refined_string_typet::index_of_int(-1)));
  axioms.push_back(a2);

  symbol_exprt qvar=fresh_univ_index("QA_index_of_string");
  string_constraintt a3(qvar, substring.length(), contains,
                        equal_exprt(str[plus_exprt(qvar, offset)],
                                    substring[qvar]));
  axioms.push_back(a3);

  return offset;
}

exprt string_constraint_generatort::add_axioms_for_last_index_of_string(
  const string_exprt &str,
  const string_exprt & substring,
  const exprt & from_index)
{
  symbol_exprt offset=fresh_exist_index("index_of");
  symbol_exprt contains=fresh_boolean("contains_substring");

  // We add axioms:
  // a1 : contains => |substring| >= length && offset <= from_index
  // a2 : !contains => offset=-1
  // a3 : forall 0 <= witness<substring.length,
  //        contains => str[witness+offset]=substring[witness]

  implies_exprt a1(contains, and_exprt
    (str.longer(plus_exprt(substring.length(), offset)),
     binary_relation_exprt(offset, ID_le, from_index)));
  axioms.push_back(a1);

  implies_exprt a2(not_exprt(contains),
                   equal_exprt(offset, refined_string_typet::index_of_int(-1)));
  axioms.push_back(a2);

  symbol_exprt qvar=fresh_univ_index("QA_index_of_string");
  equal_exprt constr3(str[plus_exprt(qvar, offset)], substring[qvar]);
  string_constraintt a3(qvar, substring.length(), contains, constr3);
  axioms.push_back(a3);

  return offset;
}


exprt string_constraint_generatort::add_axioms_for_index_of
(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(f.type()==refined_string_typet::index_type());
  string_exprt str=add_axioms_for_string_expr(args[0]);
  exprt c=args[1];
  exprt from_index;

  if(args.size()==2)
    from_index=refined_string_typet::index_zero();
  else if(args.size()==3)
    from_index=args[2];
  else
    assert(false);

  if(refined_string_typet::is_java_string_type(c.type()))
  {
    string_exprt sub=add_axioms_for_string_expr(c);
    return add_axioms_for_index_of_string(str, sub, from_index);
  }
  else
    return add_axioms_for_index_of(str, typecast_exprt(c, get_char_type()),
                                   from_index);
}

exprt string_constraint_generatort::add_axioms_for_last_index_of
(const string_exprt &str, const exprt & c, const exprt & from_index)
{
  symbol_exprt index=fresh_exist_index("last_index_of");
  symbol_exprt contains=fresh_boolean("contains_in_last_index_of");

  // We add axioms:
  // a1 : -1 <= i <= from_index
  // a2 : (i=-1 <=> !contains)
  // a3 : (contains => i <= from_index && s[i]=c)
  // a4 : forall n. i+1 <= n < from_index +1 && contains => s[n]!=c
  // a5 : forall m. 0 <= m < from_index +1 && !contains => s[m]!=c

  exprt index1=refined_string_typet::index_of_int(1);
  exprt minus1=refined_string_typet::index_of_int(-1);
  exprt from_index_plus_one=plus_exprt(from_index, index1);
  and_exprt a1(binary_relation_exprt(index, ID_ge, minus1),
               binary_relation_exprt(index, ID_lt, from_index_plus_one));
  axioms.push_back(a1);

  equal_exprt a2(not_exprt(contains), equal_exprt(index, minus1));
  axioms.push_back(a2);

  implies_exprt a3
    (contains, and_exprt(binary_relation_exprt(from_index, ID_ge, index),
                         equal_exprt(str[index], c)));
  axioms.push_back(a3);

  symbol_exprt n=fresh_univ_index("QA_last_index_of");
  string_constraintt a4(n, plus_exprt(index, index1),
                        from_index_plus_one, contains,
                        not_exprt(equal_exprt(str[n], c)));
  axioms.push_back(a4);

  symbol_exprt m=fresh_univ_index("QA_last_index_of");
  string_constraintt a5(m, from_index_plus_one, not_exprt(contains),
                        not_exprt(equal_exprt(str[m], c)));
  axioms.push_back(a5);

  return index;
}

exprt string_constraint_generatort::add_axioms_for_last_index_of
(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(f.type()==refined_string_typet::index_type());
  string_exprt str=add_axioms_for_string_expr(args[0]);
  exprt c=args[1];
  exprt from_index;

  if(args.size()==2)
    from_index=minus_exprt(str.length(), refined_string_typet::index_of_int(1));
  else if(args.size()==3)
    from_index=args[2];
  else
    assert(false);

  if(refined_string_typet::is_java_string_type(c.type()))
  {
    string_exprt sub=add_axioms_for_string_expr(c);
    return add_axioms_for_last_index_of_string(str, sub, from_index);
  }
  else
    return add_axioms_for_last_index_of
      (str, typecast_exprt(c, get_char_type()), from_index);
}

exprt string_constraint_generatort::add_axioms_for_char_literal
(const function_application_exprt &f)
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


exprt string_constraint_generatort::add_axioms_for_char_at
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 2)[0]);
  symbol_exprt char_sym=string_exprt::fresh_symbol("char", get_char_type());
  axioms.push_back(equal_exprt(char_sym, str[args(f, 2)[1]]));
  return char_sym;
}

exprt string_constraint_generatort::add_axioms_for_parse_int
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 1)[0]);
  typet type=f.type();
  symbol_exprt i=string_exprt::fresh_symbol("parsed_int", type);

  exprt zero_char=constant_char('0');
  exprt minus_char=constant_char('-');
  exprt plus_char=constant_char('+');
  assert(type.id()==ID_signedbv);
  exprt ten=from_integer(10, type);

  exprt chr=str[0];
  exprt starts_with_minus=equal_exprt(chr, minus_char);
  exprt starts_with_plus=equal_exprt(chr, plus_char);
  exprt starts_with_digit=binary_relation_exprt(chr, ID_ge, zero_char);

  for(unsigned size=1; size<=10; size++)
  {
    exprt sum=from_integer(0, type);
    exprt first_value=typecast_exprt(minus_exprt(chr, zero_char), type);

    for(unsigned j=1; j<size; j++)
    {
      sum=plus_exprt(mult_exprt(sum, ten),
                     typecast_exprt(minus_exprt(str[j], zero_char), type));
      first_value=mult_exprt(first_value, ten);
    }

    // If the length is `size`, we add axioms:
    // a1 : starts_with_digit => i=sum+first_value
    // a2 : starts_with_plus => i=sum
    // a3 : starts_with_minus => i=-sum

    equal_exprt premise=str.has_length(size);
    implies_exprt a1(and_exprt(premise, starts_with_digit),
                     equal_exprt(i, plus_exprt(sum, first_value)));
    axioms.push_back(a1);

    implies_exprt a2(and_exprt(premise, starts_with_plus), equal_exprt(i, sum));
    axioms.push_back(a2);

    implies_exprt a3(and_exprt(premise, starts_with_minus),
                     equal_exprt(i, unary_minus_exprt(sum)));
    axioms.push_back(a3);
  }
  return i;
}


exprt string_constraint_generatort::is_high_surrogate(const exprt & chr) const
{
  return and_exprt
    (binary_relation_exprt(chr, ID_ge, constant_char(0xD800)),
     binary_relation_exprt(chr, ID_le, constant_char(0xDBFF)));
}

exprt string_constraint_generatort::is_low_surrogate(const exprt & chr) const
{
  return and_exprt
    (binary_relation_exprt(chr, ID_ge, constant_char(0xDC00)),
     binary_relation_exprt(chr, ID_le, constant_char(0xDFFF)));
}

// pair_value=0x10000+(((char1%0x0800)*0x0400)+char2%0x0400)
// char1 and char2 should be of type return_type
exprt pair_value(exprt char1, exprt char2, typet return_type)
{
  exprt hex010000=from_integer(0x010000, return_type);
  exprt hex0800=from_integer(0x0800, return_type);
  exprt hex0400=from_integer(0x0400, return_type);
  mult_exprt m1(mod_exprt(char1, hex0800), hex0400);
  mod_exprt m2(char2, hex0400);
  plus_exprt pair_value(hex010000, plus_exprt(m1, m2));
  return pair_value;
}

exprt string_constraint_generatort::add_axioms_for_code_point_at
(const function_application_exprt &f)
{
  typet return_type=f.type();
  assert(return_type.id()==ID_signedbv);
  string_exprt str=add_axioms_for_string_expr(args(f, 2)[0]);
  exprt pos=args(f, 2)[1];

  symbol_exprt result=string_exprt::fresh_symbol("char", return_type);
  exprt index1=refined_string_typet::index_of_int(1);
  exprt char1=str[pos];
  exprt char2=str[plus_exprt(pos, index1)];
  exprt char1_as_int=typecast_exprt(char1, return_type);
  exprt char2_as_int=typecast_exprt(char2, return_type);
  exprt pair=pair_value(char1_as_int, char2_as_int, return_type);
  exprt is_low=is_low_surrogate(str[plus_exprt(pos, index1)]);
  exprt return_pair=and_exprt(is_high_surrogate(str[pos]), is_low);

  axioms.push_back(implies_exprt(return_pair, equal_exprt(result, pair)));
  axioms.push_back(implies_exprt(not_exprt(return_pair),
                                 equal_exprt(result, char1_as_int)));
  return result;
}

exprt string_constraint_generatort::add_axioms_for_code_point_before
(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  assert(args.size()==2);
  typet return_type=f.type();
  assert(return_type.id()==ID_signedbv);
  symbol_exprt result=string_exprt::fresh_symbol("char", return_type);
  string_exprt str=add_axioms_for_string_expr(args[0]);

  exprt char1=str[minus_exprt(args[1], refined_string_typet::index_of_int(2))];
  exprt char2=str[minus_exprt(args[1], refined_string_typet::index_of_int(1))];
  exprt char1_as_int=typecast_exprt(char1, return_type);
  exprt char2_as_int=typecast_exprt(char2, return_type);

  exprt pair=pair_value(char1_as_int, char2_as_int, return_type);
  exprt return_pair=
    and_exprt(is_high_surrogate(char1), is_low_surrogate(char2));

  axioms.push_back(implies_exprt(return_pair, equal_exprt(result, pair)));
  axioms.push_back(implies_exprt(not_exprt(return_pair),
                                 equal_exprt(result, char2_as_int)));
  return result;
}

exprt string_constraint_generatort::add_axioms_for_code_point_count
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 3)[0]);
  exprt begin=args(f, 3)[1];
  exprt end=args(f, 3)[2];
  typet return_type=f.type();
  symbol_exprt result=
    string_exprt::fresh_symbol("code_point_count", return_type);

  exprt length=minus_exprt(end, begin);
  exprt minimum=div_exprt(length, refined_string_typet::index_of_int(2));
  axioms.push_back(binary_relation_exprt(result, ID_le, length));
  axioms.push_back(binary_relation_exprt(result, ID_ge, minimum));

  return result;
}

exprt string_constraint_generatort::add_axioms_for_offset_by_code_point
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 3)[0]);
  exprt index=args(f, 3)[1];
  exprt offset=args(f, 3)[2];
  typet return_type=f.type();
  symbol_exprt result=
    string_exprt::fresh_symbol("offset_by_code_point", return_type);

  exprt minimum=plus_exprt(index, offset);
  exprt maximum=plus_exprt(index, plus_exprt(offset, offset));
  axioms.push_back(binary_relation_exprt(result, ID_le, maximum));
  axioms.push_back(binary_relation_exprt(result, ID_ge, minimum));

  return result;
}


exprt string_constraint_generatort::add_axioms_for_to_char_array
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 1)[0]);
  return str.content();
}


exprt string_constraint_generatort::add_axioms_for_compare_to
(const function_application_exprt &f)
{
  string_exprt s1=add_axioms_for_string_expr(args(f, 2)[0]);
  string_exprt s2=add_axioms_for_string_expr(args(f, 2)[1]);
  typet return_type=f.type();
  symbol_exprt res=string_exprt::fresh_symbol("compare_to", return_type);

  // In the lexicographic comparison, x is the first point where the two
  // strings differ.
  // We add axioms:
  // a1 : res==0 => |s1|=|s2|
  // a2 : forall i<|s1|. s1[i]==s2[i]
  // a3 : exists x.
  // res!=0 ==> x> 0 &&
  //   ((|s1| <= |s2| && x<|s1|) || (|s1| >= |s2| && x<|s2|)
  //   && res=s1[x]-s2[x] )
  // || cond2:
  //   (|s1|<|s2| && x=|s1|) || (|s1| > |s2| && x=|s2|) && res=|s1|-|s2|)
  // a4 : forall i<x. res!=0 => s1[i]=s2[i]

  assert(return_type.id()==ID_signedbv);

  equal_exprt res_null=equal_exprt(res, from_integer(0, return_type));
  implies_exprt a1(res_null, s1.same_length(s2));
  axioms.push_back(a1);

  symbol_exprt i=fresh_univ_index("QA_compare_to");
  string_constraintt a2(i, s1.length(), res_null, equal_exprt(s1[i], s2[i]));
  axioms.push_back(a2);

  symbol_exprt x=fresh_exist_index("index_compare_to");
  equal_exprt ret_char_diff
    (res, typecast_exprt(minus_exprt(s1[x], s2[x]), return_type));
  equal_exprt ret_length_diff
    (res, typecast_exprt(minus_exprt(s1.length(), s2.length()), return_type));
  or_exprt guard1(and_exprt(s1.shorter(s2), s1.strictly_longer(x)),
                  and_exprt(s1.longer(s2), s2.strictly_longer(x)));
  and_exprt cond1(ret_char_diff, guard1);
  or_exprt guard2(and_exprt(s2.strictly_longer(s1), s1.has_length(x)),
                  and_exprt(s1.strictly_longer(s2), s2.has_length(x)));
  and_exprt cond2(ret_length_diff, guard2);

  implies_exprt a3
    (not_exprt(res_null),
     and_exprt(binary_relation_exprt(x, ID_ge, from_integer(0, return_type)),
               or_exprt(cond1, cond2)));
  axioms.push_back(a3);

  string_constraintt a4(i, x, not_exprt(res_null), equal_exprt(s1[i], s2[i]));
  axioms.push_back(a4);

  return res;
}

symbol_exprt string_constraint_generatort::add_axioms_for_intern
(const function_application_exprt &f)
{
  string_exprt str=add_axioms_for_string_expr(args(f, 1)[0]);
  typet return_type=f.type();

  // initialisation of the missing pool variable
  std::map<irep_idt, string_exprt>::iterator it;
  for(it=symbol_to_string.begin(); it!=symbol_to_string.end(); it++)
    if(pool.find(it->second)==pool.end())
      pool[it->second]=string_exprt::fresh_symbol("pool", return_type);

  // intern(str)=s_0 || s_1 || ...
  // for each string s.
  //    intern(str)=intern(s) || |str|!=|s|
  //    || (|str|==|s| && exists i<|s|. s[i]!=str[i])

  // symbol_exprt intern=string_exprt::fresh_symbol("intern",return_type);

  exprt disj=false_exprt();
  for(it=symbol_to_string.begin(); it!=symbol_to_string.end(); it++)
    disj=or_exprt
      (disj, equal_exprt(pool[str], symbol_exprt(it->first, return_type)));

  axioms.push_back(disj);


  // WARNING: the specification may be incomplete or incorrect
  for(it=symbol_to_string.begin(); it!=symbol_to_string.end(); it++)
    if(it->second!=str)
    {
      symbol_exprt i=fresh_exist_index("index_intern");
      axioms.push_back
        (or_exprt
          (equal_exprt(pool[it->second], pool[str]),
           or_exprt
             (not_exprt(str.same_length(it->second)),
              and_exprt
                (str.same_length(it->second),
                 and_exprt
                   (not_exprt(equal_exprt(str[i], it->second[i])),
                    and_exprt(str.strictly_longer(i), is_positive(i)))))));
    }


  return pool[str];
}


void string_constraint_generatort::set_string_symbol_equal_to_expr
(const symbol_exprt & sym, const exprt & str)
{
  if(str.id()==ID_symbol)
    assign_to_symbol(sym, find_or_add_string_of_symbol(to_symbol_expr(str)));
  else
    assign_to_symbol(sym, add_axioms_for_string_expr(str));
}

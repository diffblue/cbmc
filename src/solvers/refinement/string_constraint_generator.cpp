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

constant_exprt string_constraint_generatort::constant_char(int i)
{
  switch(language) 
    {
    case C :
      return constant_exprt(integer2binary(i,STRING_SOLVER_CHAR_WIDTH),refined_string_typet::char_type());
      break;
    case JAVA : return constant_exprt(integer2binary(i,JAVA_STRING_SOLVER_CHAR_WIDTH),refined_string_typet::java_char_type());
      break;
    default: assert(false);
    }
}


constant_exprt string_constraint_generatort::constant_unsigned(int i, size_t width)
{ return constant_exprt(integer2binary(i,width),unsignedbv_typet(width)); }

constant_exprt string_constraint_generatort::constant_signed(int i, size_t width)
{ return constant_exprt(integer2binary(i,width),signedbv_typet(width)); }

void string_constraint_generatort::check_char_type(const exprt & str) 
{
  if(language == C)
    assert(refined_string_typet::is_c_string_type(str.type()));
  else
    if(language == UNKNOWN)
      {
	if(refined_string_typet::is_c_string_type(str.type()))
	  language = C;
	else
	  language = JAVA;
      }

}

unsignedbv_typet string_constraint_generatort::get_char_type()
{ 
  if(language==C)
    return refined_string_typet::char_type();
  else if(language==JAVA) return refined_string_typet::java_char_type();
  else assert(false);
}

size_t string_constraint_generatort::get_char_width()
{ 
  if(language==C)
    return STRING_SOLVER_CHAR_WIDTH;
  else if(language==JAVA) return JAVA_STRING_SOLVER_CHAR_WIDTH;
  else assert(false);
}

symbol_exprt string_constraint_generatort::fresh_univ_index(const irep_idt &prefix)
{
  return string_exprt::fresh_symbol(prefix,refined_string_typet::index_type());
}

symbol_exprt string_constraint_generatort::fresh_exist_index(const irep_idt &prefix)
{
  symbol_exprt s = string_exprt::fresh_symbol(prefix,refined_string_typet::index_type());
  index_symbols.push_back(s);
  return s;
}

symbol_exprt string_constraint_generatort::fresh_boolean(const irep_idt &prefix)
{
  symbol_exprt b = string_exprt::fresh_symbol(prefix,bool_typet());
  boolean_symbols.push_back(b);
  return b;
}


string_exprt string_constraint_generatort::string_of_expr(const exprt & unrefined_string)
{
  string_exprt s;
    
  check_char_type(unrefined_string);

  if(unrefined_string.id() == ID_function_application)
    {
      exprt res = function_application(to_function_application_expr(unrefined_string));
      assert(res.type() == refined_string_typet(get_char_type()));
      s = to_string_expr(res);
    }
  else if(unrefined_string.id()==ID_symbol) 
    s = get_string_of_symbol(to_symbol_expr(unrefined_string));
  else if(unrefined_string.id()==ID_address_of)
    {
      assert(unrefined_string.op0().id()==ID_symbol);
      s = get_string_of_symbol(to_symbol_expr(unrefined_string.op0()));
    }
  else if(unrefined_string.id()==ID_if) 
    s = string_if(to_if_expr(unrefined_string));
  else if(unrefined_string.id()==ID_nondet_symbol || unrefined_string.id()==ID_struct) {
    // We ignore non deterministic symbols and struct
  }
  else
    {
      throw ("string_exprt of:\n" + unrefined_string.pretty() 
	     + "\nwhich is not a function application, a symbol or an if expression");
    }

  axioms.emplace_back(s.longer(refined_string_typet::index_zero()));
  return s;
}



string_exprt string_constraint_generatort::string_if(const if_exprt &expr)
{
  string_exprt res(get_char_type());
  assert(refined_string_typet::is_unrefined_string_type(expr.true_case().type()));
  string_exprt t = string_of_expr(expr.true_case());
  assert(refined_string_typet::is_unrefined_string_type(expr.false_case().type()));
  string_exprt f = string_of_expr(expr.false_case());

  axioms.emplace_back(expr.cond(),res.same_length(t));
  symbol_exprt qvar = fresh_univ_index("QA_string_if_true");
  axioms.push_back(string_constraintt(expr.cond(),equal_exprt(res[qvar],t[qvar])).forall(qvar,t.length()));
  
  axioms.emplace_back(not_exprt(expr.cond()),res.same_length(f));
  symbol_exprt qvar2 = fresh_univ_index("QA_string_if_false");
  axioms.push_back(string_constraintt(not_exprt(expr.cond()),equal_exprt(res[qvar2],f[qvar2])).forall(qvar2,f.length()));
  return res;
}


string_exprt string_constraint_generatort::get_string_of_symbol(const symbol_exprt & sym) 
{
  irep_idt id = sym.get_identifier();
  std::map<irep_idt, string_exprt>::iterator f = symbol_to_string.find(id);
  if(f != symbol_to_string.end())
    return f->second;

  symbol_to_string[id]= string_exprt(get_char_type());
  return symbol_to_string[id];
}

string_exprt string_constraint_generatort::string_of_symbol(const symbol_exprt & sym)
{
  if(refined_string_typet::is_java_string_type(sym.type()) 
     && starts_with(std::string(sym.get(ID_identifier).c_str()),"java::java.lang.String.Literal.")) 
    {
      assert(false); // is this branch used ?
      string_exprt s;
      s = string_constant(string_exprt::extract_java_string(sym),JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
    return s;
  }
  else {
    return get_string_of_symbol(sym);
  }
}  


exprt string_constraint_generatort::function_application
(const function_application_exprt & expr)
{
  const exprt &name = expr.function();
  assert(name.id() == ID_symbol);

  const irep_idt &id = to_symbol_expr(name).get_identifier();
  if (starts_with(id,cprover_char_literal_func)) 
    return char_literal(expr);
  else if (starts_with(id,cprover_string_length_func)) 
    return string_length(expr);
  else if (starts_with(id,cprover_string_equal_func)) 
    return string_equal(expr);
  else if (starts_with(id,cprover_string_equals_ignore_case_func)) 
    return string_equals_ignore_case(expr);
  else if (starts_with(id,cprover_string_is_empty_func)) 
    return string_is_empty(expr);
  else if (starts_with(id,cprover_string_char_at_func)) 
    return string_char_at(expr);
  else if (starts_with(id,cprover_string_is_prefix_func)) 
    return string_is_prefix(expr);
  else if (starts_with(id,cprover_string_is_suffix_func)) 
    return string_is_suffix(expr);
  else if (starts_with(id,cprover_string_startswith_func)) 
    return string_is_prefix(expr,true);
  else if (starts_with(id,cprover_string_endswith_func)) 
    return string_is_suffix(expr,true);
  else if (starts_with(id,cprover_string_contains_func)) 
    return string_contains(expr);
  else if (starts_with(id,cprover_string_hash_code_func)) 
    return string_hash_code(expr);
  else if (starts_with(id,cprover_string_index_of_func)) 
    return string_index_of(expr);
  else if (starts_with(id,cprover_string_last_index_of_func)) 
    return string_last_index_of(expr);
  else if (starts_with(id,cprover_string_parse_int_func)) 
    return string_parse_int(expr);
  else if (starts_with(id,cprover_string_to_char_array_func)) 
    return string_to_char_array(expr);
  else if (starts_with(id,cprover_string_code_point_at_func)) 
    return string_code_point_at(expr);
  else if (starts_with(id,cprover_string_code_point_before_func)) 
    return string_code_point_before(expr);
  else if (starts_with(id,cprover_string_code_point_count_func)) 
    return string_code_point_count(expr);
  else if (starts_with(id,cprover_string_offset_by_code_point_func)) 
    return string_offset_by_code_point(expr);
  else if (starts_with(id,cprover_string_compare_to_func)) 
    return string_compare_to(expr);
  else if(starts_with(id,cprover_string_literal_func))
    return string_literal(expr);
  else if(starts_with(id,cprover_string_concat_func))
    return string_concat(expr);
  else if(starts_with(id,cprover_string_concat_int_func))
    return string_concat_int(expr);
  else if(starts_with(id,cprover_string_concat_long_func))
    return string_concat_long(expr);
  else if(starts_with(id,cprover_string_concat_bool_func))
      return string_concat_bool(expr);
  else if(starts_with(id,cprover_string_concat_char_func))
    return string_concat_char(expr);
  else if(starts_with(id,cprover_string_concat_double_func))
    return string_concat_double(expr);
  else if(starts_with(id,cprover_string_concat_float_func))
    return string_concat_float(expr);
  else if(starts_with(id,cprover_string_concat_code_point_func))
    return string_concat_code_point(expr);
  else if(starts_with(id,cprover_string_insert_func))
    return string_insert(expr);
  else if(starts_with(id,cprover_string_insert_int_func))
    return string_insert_int(expr);
  else if(starts_with(id,cprover_string_insert_long_func))
    return string_insert_long(expr);
  else if(starts_with(id,cprover_string_insert_bool_func))
    return string_insert_bool(expr);
  else if(starts_with(id,cprover_string_insert_char_func))
    return string_insert_char(expr);
  else if(starts_with(id,cprover_string_insert_double_func))
    return string_insert_double(expr);
  else if(starts_with(id,cprover_string_insert_float_func))
    return string_insert_float(expr);
  else if(starts_with(id,cprover_string_substring_func))
    return string_substring(expr);
  else if(starts_with(id,cprover_string_trim_func))
    return string_trim(expr);
  else if(starts_with(id,cprover_string_to_lower_case_func))
    return string_to_lower_case(expr);
  else if(starts_with(id,cprover_string_to_upper_case_func))
    return string_to_upper_case(expr);
  else if(starts_with(id,cprover_string_char_set_func))
    return string_char_set(expr);
  else if(starts_with(id,cprover_string_value_of_func))
    return string_value_of(expr);
  else if(starts_with(id,cprover_string_empty_string_func))
    return empty_string(expr);
  else if(starts_with(id,cprover_string_copy_func))
    return string_copy(expr);
  else if(starts_with(id,cprover_string_of_int_func))
    return of_int(expr);
  else if(starts_with(id,cprover_string_of_int_hex_func))
    return of_int_hex(expr);
  else if(starts_with(id,cprover_string_of_float_func))
    return of_float(expr);
  else if(starts_with(id,cprover_string_of_double_func))
    return of_double(expr);
  else if(starts_with(id,cprover_string_of_long_func))
    return of_long(expr);
  else if(starts_with(id,cprover_string_of_bool_func))
    return of_bool(expr);
  else if(starts_with(id,cprover_string_of_char_func))
    return of_char(expr);
  else if(starts_with(id,cprover_string_set_length_func))
    return string_set_length(expr);
  else if(starts_with(id,cprover_string_delete_func))
    return string_delete(expr);
  else if(starts_with(id,cprover_string_delete_char_at_func))
    return string_delete_char_at(expr);
  else if(starts_with(id,cprover_string_replace_func))
    return string_replace(expr);
  else if(starts_with(id,cprover_string_format_func))
    return string_format(expr);
  else if(starts_with(id,cprover_string_data_func))
    return string_data(expr);
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
  std::string value = tmp.substr(31);
  return irep_idt(value);
}

string_exprt string_constraint_generatort::string_constant(irep_idt sval, int char_width, unsignedbv_typet char_type){

  string_exprt res(char_type);
  std::string str = sval.c_str();
  // should only do this for java
  std::wstring utf16 = utf8_to_utf16(str);
  // warning: endianness should be used as a flag when using this function
  
  for (std::size_t i = 0; i < utf16.size(); ++i) {
    std::string idx_binary = integer2binary(i,STRING_SOLVER_INDEX_WIDTH);
    constant_exprt idx(idx_binary, refined_string_typet::index_type());
    // warning: this should disappear if utf8_to_utf16 takes into account endianness
    wchar_t big_endian = ((utf16[i] << 8) & 0xFF00) | (utf16[i] >> 8);

    std::string sval_binary=integer2binary((unsigned)big_endian, char_width);
    constant_exprt c(sval_binary,char_type);
    equal_exprt lemma(res[idx], c);
    axioms.emplace_back(lemma,true);
  }
  
  std::string s_length_binary = integer2binary(unsigned(utf16.size()),STRING_SOLVER_INDEX_WIDTH);
  exprt s_length = constant_exprt(s_length_binary, refined_string_typet::index_type());

  axioms.emplace_back(res.has_length(s_length));
  return res;
}
				   
string_exprt string_constraint_generatort::empty_string(const function_application_exprt &f)
{
  assert(f.arguments().size() == 0); 
  string_exprt res(get_char_type());
  axioms.emplace_back(res.has_length(0));
  return res;
}

string_exprt string_constraint_generatort::string_literal(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); //bad args to string literal?

  const exprt &arg = args[0];

  irep_idt sval; 
  int char_width;
  unsignedbv_typet char_type;
  
  if (arg.operands().size() == 1 &&
      arg.op0().operands().size() == 1 &&
      arg.op0().op0().operands().size() == 2 &&
      arg.op0().op0().op0().id() == ID_string_constant) {
    // C string constant
      
    const exprt &s = arg.op0().op0().op0();
    sval = to_string_constant(s).get_value();
    char_width = STRING_SOLVER_CHAR_WIDTH;
    char_type = refined_string_typet::char_type();

  } else {
    // Java string constant
    assert (arg.operands().size() == 1); 
    assert(refined_string_typet::is_unrefined_string_type(arg.type()));
    const exprt &s = arg.op0();
    
    //it seems the value of the string is lost, we need to recover it from the identifier
    sval = extract_java_string(to_symbol_expr(s));
    char_width = JAVA_STRING_SOLVER_CHAR_WIDTH;
    char_type = refined_string_typet::java_char_type();
  }

  return string_constant(sval,char_width,char_type);
}


string_exprt string_constraint_generatort::string_concat(const string_exprt & s1, const string_exprt & s2)
{
  // |res| = |s1| + |s2|
  string_exprt res(get_char_type());
  axioms.emplace_back(res.has_length(plus_exprt(s1.length(), s2.length())));
  axioms.emplace_back(s1.shorter(res)); // we have to be careful about very long strings
  axioms.emplace_back(s2.shorter(res));

  // forall i<|s1|. res[i] = s1[i]
  symbol_exprt idx = fresh_univ_index("QA_index_concat");
  string_constraintt a1(equal_exprt(s1[idx],res[idx]));
  axioms.push_back(a1.forall(idx, s1.length()));

  // forall i<|s2|. res[i+|s1|] = s2[i]
  symbol_exprt idx2 = fresh_univ_index("QA_index_concat2");
  string_constraintt a2(equal_exprt(s2[idx2],res[plus_exprt(idx2,s1.length())]));
  axioms.push_back(a2.forall(idx2, s2.length()));

  return res;
}


string_exprt string_constraint_generatort::string_concat(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  
  string_exprt s1 = string_of_expr(args[0]);
  string_exprt s2 = string_of_expr(args[1]);

  return string_concat(s1, s2);
}


string_exprt string_constraint_generatort::string_copy(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,1)[0]);
  string_exprt res(get_char_type());
  axioms.emplace_back(res.same_length(s1));
  symbol_exprt idx = fresh_univ_index("QA_index_copy");
  string_constraintt a1(equal_exprt(s1[idx],res[idx]));
  axioms.push_back(a1.forall(idx, s1.length()));  
  return res;
}

string_exprt string_constraint_generatort::string_set_length(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,2)[0]);
  exprt k = args(f,2)[1];
  string_exprt res(get_char_type());

  // |s| = k 
  // && forall i < k. (i < k ==> s[i] = s1[i]) && (i >= k ==> s[i] = 0)

  axioms.emplace_back(res.has_length(k));
  symbol_exprt idx = fresh_univ_index("QA_index_set_length");
  string_constraintt a1
    (and_exprt(implies_exprt(s1.strictly_longer(idx), equal_exprt(s1[idx],res[idx])),
	       implies_exprt(s1.shorter(idx), equal_exprt(s1[idx],constant_char(0)))));
  axioms.push_back(a1.forall(idx, k));  

  return res;
}


string_exprt string_constraint_generatort::java_char_array(const exprt & char_array)
{
  string_exprt res(get_char_type());
  exprt arr = to_address_of_expr(char_array).object();
  exprt len = member_exprt(arr, "length", res.length().type());
  exprt cont = member_exprt(arr, "data", res.content().type());
  res.op0() = len;
  res.op1() = cont;
  return res;
}
 

string_exprt string_constraint_generatort::string_value_of(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  if(args.size() == 3)
    {
      string_exprt res(get_char_type());
      exprt char_array = args[0];
      exprt offset = args[1];
      exprt count = args[2];
      string_exprt str = java_char_array(char_array);
      axioms.emplace_back(res.has_length(count));
      symbol_exprt idx = fresh_univ_index("QA_index_value_of");
      string_constraintt a1(equal_exprt(str[plus_exprt(idx,offset)],res[idx]));
      axioms.push_back(a1.forall(idx, count));
      return res;
    }
  else
    {
      assert(args.size() == 1);
      return java_char_array(args[0]);
    }
}

string_exprt string_constraint_generatort::string_substring
(const function_application_exprt &f)
{
  assert(f.arguments().size() >= 2);
  string_exprt str = string_of_expr(f.arguments()[0]);
  exprt i(f.arguments()[1]);
  exprt j;
  if(f.arguments().size() == 3) j = f.arguments()[2];
  else { assert(f.arguments().size() == 2); j = str.length(); }
  return string_substring(str,i,j);
}

string_exprt string_constraint_generatort::string_substring
  (const string_exprt & str, const exprt & start, const exprt & end)
{
  symbol_exprt idx = fresh_exist_index("index_substring");
  assert(start.type() == refined_string_typet::index_type());
  assert(end.type() == refined_string_typet::index_type());
  string_exprt res(get_char_type());

  axioms.emplace_back(binary_relation_exprt(start, ID_lt, end),res.has_length(minus_exprt(end, start)));
  axioms.emplace_back(binary_relation_exprt(start, ID_ge, end),res.has_length(refined_string_typet::index_zero()));
  // Warning: check what to do if the string is not long enough
  axioms.emplace_back(str.longer(end));

  // forall idx < str.length, str[idx] = arg_str[idx+i]
  string_constraintt a(equal_exprt(res[idx], str[plus_exprt(start, idx)]));
  axioms.push_back(a.forall(idx,res.length()));
  return res;
}

string_exprt string_constraint_generatort::string_trim
(const function_application_exprt &expr)
{
  string_exprt str = string_of_expr(args(expr,1)[0]);
  string_exprt res(get_char_type());
  symbol_exprt idx = fresh_exist_index("index_trim");
  exprt space_char = constant_char(32);

  // m + |s1| <= |str|
  axioms.emplace_back(str.longer(plus_exprt(idx, res.length())));
  axioms.emplace_back(binary_relation_exprt(idx, ID_ge, refined_string_typet::index_zero()));
  axioms.emplace_back(str.longer(idx));
  axioms.emplace_back(res.longer(refined_string_typet::index_zero()));
  axioms.emplace_back(res.shorter(str)); // necessary to prevent exceeding the biggest integer

  symbol_exprt n = fresh_univ_index("QA_index_trim");
  // forall n < m, str[n] = ' '
  string_constraintt a(equal_exprt(str[n], space_char));
  axioms.push_back(a.forall(n,idx));

  symbol_exprt n2 = fresh_univ_index("QA_index_trim2");
  // forall n < |str|-m-|s1|, str[m+|s1|+n] = ' '
  string_constraintt a1(equal_exprt(str[plus_exprt(idx,plus_exprt(res.length(),n2))], space_char));
  axioms.push_back(a1.forall(n2,minus_exprt(str.length(),plus_exprt(idx,res.length()))));

  symbol_exprt n3 = fresh_univ_index("QA_index_trim3");
  // forall n < |s1|, s[idx+n] = s1[n]
  string_constraintt a2(equal_exprt(res[n3], str[plus_exprt(n3, idx)]));
  axioms.push_back(a2.forall(n3,res.length()));
  // (s[m] != ' ' && s[m+|s1|-1] != ' ') || m = |s|
  or_exprt m_index_condition(equal_exprt(idx,str.length()),
			     and_exprt
			     (not_exprt(equal_exprt(str[idx],space_char)),
			      not_exprt(equal_exprt(str[minus_exprt(plus_exprt(idx,res.length()),refined_string_typet::index_of_int(1))],space_char))));
  axioms.push_back(m_index_condition);
  return res;
}

string_exprt string_constraint_generatort::string_to_lower_case
(const function_application_exprt &expr)
{
  string_exprt str = string_of_expr(args(expr,1)[0]);
  string_exprt res(get_char_type());
  exprt char_a = constant_char(97);
  exprt char_A = constant_char(65);
  exprt char_z = constant_char(122);
  exprt char_Z = constant_char(90);

  axioms.emplace_back(res.same_length(str));

  symbol_exprt idx = fresh_univ_index("QA_lower_case");
  // forall idx < str.length, this[idx] = 'A'<=str[idx]<='Z' ? str[idx]+'a'-'A' : str[idx]
  exprt is_upper_case = and_exprt(binary_relation_exprt(char_A,ID_le,str[idx]),
				  binary_relation_exprt(str[idx],ID_le,char_Z));
  equal_exprt convert(res[idx],plus_exprt(str[idx],minus_exprt(char_a,char_A)));
  equal_exprt eq(res[idx], str[idx]);
  string_constraintt a(and_exprt(implies_exprt(is_upper_case,convert),implies_exprt(not_exprt(is_upper_case),eq)));
  axioms.push_back(a.forall(idx,res.length()));
  return res;
}


string_exprt string_constraint_generatort::string_to_upper_case
(const function_application_exprt &expr)
{
  string_exprt str = string_of_expr(args(expr,1)[0]);
  string_exprt res(get_char_type());
  exprt char_a = constant_char(97);
  exprt char_A = constant_char(65);
  exprt char_z = constant_char(122);
  exprt char_Z = constant_char(90);

  axioms.emplace_back(res.same_length(str));

  symbol_exprt idx = fresh_univ_index("QA_upper_case");
  // forall idx < str.length, this[idx] = 'a'<=str[idx]<='z' ? str[idx]+'A'-'a' : str[idx]
  exprt is_lower_case = and_exprt(binary_relation_exprt(char_a,ID_le,str[idx]),
				  binary_relation_exprt(str[idx],ID_le,char_z));
  equal_exprt convert(res[idx],plus_exprt(str[idx],minus_exprt(char_A,char_a)));
  equal_exprt eq(res[idx], str[idx]);
  string_constraintt a(and_exprt(implies_exprt(is_lower_case,convert),implies_exprt(not_exprt(is_lower_case),eq)));
  axioms.push_back(a.forall(idx,res.length()));
  return res;
}


string_exprt string_constraint_generatort::of_int
(const function_application_exprt &expr)
{ return of_int(args(expr,1)[0],10); }

string_exprt string_constraint_generatort::of_long
(const function_application_exprt &expr)
{ return of_int(args(expr,1)[0],30); }

string_exprt string_constraint_generatort::of_float
(const function_application_exprt &f)
{ return of_float(args(f,1)[0],false); }

string_exprt string_constraint_generatort::of_double
(const function_application_exprt &f)
{ return of_float(args(f,1)[0],true); }

string_exprt string_constraint_generatort::of_float
(const exprt &f, bool double_precision)
{
  // Warning: we currently only have partial specification
  unsignedbv_typet char_type = get_char_type();
  size_t char_width = get_char_width();

  string_exprt res(char_type);
  axioms.emplace_back(res.shorter(refined_string_typet::index_of_int(24)));


  string_exprt magnitude(char_type);
  string_exprt sign_string(char_type);

  //     If the argument is NaN, the result is the string "NaN".
  string_exprt nan_string = string_constant("NaN",char_width,char_type);

  ieee_float_spect fspec = double_precision?ieee_float_spect::double_precision():ieee_float_spect::single_precision();
  
  exprt isnan = float_bvt().isnan(f,fspec);
  axioms.emplace_back(isnan, magnitude.same_length(nan_string));
  symbol_exprt qvar = fresh_univ_index("QA_equal_nan");
  axioms.push_back
    (string_constraintt(isnan,equal_exprt(magnitude[qvar],nan_string[qvar])
			).forall(qvar,nan_string.length()));

  // If the argument is not NaN, the result is a string that represents the sign and magnitude (absolute value) of the argument. If the sign is negative, the first character of the result is '-' ('\u002D'); if the sign is positive, no sign character appears in the result. 

  const bitvector_typet &bv_type=to_bitvector_type(f.type());
  unsigned width=bv_type.get_width();
  exprt isneg = extractbit_exprt(f, width-1);

  axioms.emplace_back(isneg, sign_string.has_length(1));
  
  axioms.emplace_back(not_exprt(isneg), sign_string.has_length(0));
  axioms.emplace_back(isneg,equal_exprt(sign_string[0], constant_char(0x2D)));

  // If m is infinity, it is represented by the characters "Infinity"; thus, positive infinity produces the result "Infinity" and negative infinity produces the result "-Infinity".
  
  string_exprt infinity_string = string_constant("Infinity",char_width,char_type);
  exprt isinf = float_bvt().isinf(f,fspec);
  axioms.emplace_back(isinf, magnitude.same_length(infinity_string));
  symbol_exprt qvar_inf = fresh_univ_index("QA_equal_infinity");
  axioms.push_back
    (string_constraintt(isinf,equal_exprt(magnitude[qvar_inf],infinity_string[qvar_inf])
			).forall(qvar_inf,infinity_string.length()));

  //If m is zero, it is represented by the characters "0.0"; thus, negative zero produces the result "-0.0" and positive zero produces the result "0.0".

  string_exprt zero_string = string_constant("0.0",char_width,char_type);
  exprt iszero = float_bvt().is_zero(f,fspec);
  axioms.emplace_back(iszero, magnitude.same_length(zero_string));
  symbol_exprt qvar_zero = fresh_univ_index("QA_equal_zero");
  axioms.push_back
    (string_constraintt(iszero,equal_exprt(magnitude[qvar_zero],zero_string[qvar_zero])
			).forall(qvar_zero,zero_string.length()));

  return string_concat(sign_string,magnitude);
  
  /*
  ieee_floatt milli(fspec);
  milli.from_float(0.001);
  ieee_floatt decamega(fspec);
  decamega.from_float(1e7);
  exprt scientific = or_exprt
    (float_bvt().relation(f,float_bvt().LT,milli.to_expr(),fspec),
     float_bvt().relation(f,float_bvt().GE,decamega.to_expr(),fspec));
  */

  //      If m is greater than or equal to 10^-3 but less than 10^7, then it is represented as the integer part of m, in decimal form with no leading zeroes, followed by '.' ('\u002E'), followed by one or more decimal digits representing the fractional part of m.
  
  //string_exprt integer_part(char_type);
  //exprt integer = float_bvt().to_integer(float_bvt.abs(f,fspec),32,true,fspec);  
  
  //integer_part.of_int(integer);
  //string_exprt dot_string(char_type);
  //dot_string.of_string_constant(".",char_width,char_type,axioms);

  //string_exprt fractional_part(char_type);

  /* Here is the remainder of the specification of Float.toString, for the magnitude m : 

        If m is less than 10^-3 or greater than or equal to 10^7, then it is represented in so-called "computerized scientific notation." Let n be the unique integer such that 10n ≤ m < 10n+1; then let a be the mathematically exact quotient of m and 10n so that 1 ≤ a < 10. The magnitude is then represented as the integer part of a, as a single decimal digit, followed by '.' ('\u002E'), followed by decimal digits representing the fractional part of a, followed by the letter 'E' ('\u0045'), followed by a representation of n as a decimal integer, as produced by the method Integer.toString(int). 

	How many digits must be printed for the fractional part of m or a? There must be at least one digit to represent the fractional part, and beyond that as many, but only as many, more digits as are needed to uniquely distinguish the argument value from adjacent values of type float. That is, suppose that x is the exact mathematical value represented by the decimal representation produced by this method for a finite nonzero argument f. Then f must be the float value nearest to x; or, if two float values are equally close to x, then f must be one of them and the least significant bit of the significand of f must be 0.  */

  /*
  exprt char_0 = constant_of_nat(48,char_width,char_type);
  exprt char_9 = constant_of_nat(57,char_width,char_type);
  exprt char_dot = constant_of_nat(46,char_width,char_type);

  symbol_exprt idx = fresh_symbol("QA_float",refined_string_typet::index_type());
  exprt c = (*this)[idx];
  exprt is_digit = 
    or_exprt(and_exprt(binary_relation_exprt(char_0,ID_le,c),
		       binary_relation_exprt(c,ID_le,char_9)),
	     equal_exprt(c,char_dot)
	     );
	     string_constraintt a(is_digit);*/
  //axioms.push_back(a.forall(idx,index_zero,length()));
}




string_exprt string_constraint_generatort::of_bool
(const function_application_exprt &f)
{
  return of_bool(args(f,1)[0]);
}


string_exprt string_constraint_generatort::of_bool(const exprt &i)
{
  unsignedbv_typet char_type = get_char_type();
  int char_width = get_char_width();
  string_exprt res(char_type);

  assert(i.type() == bool_typet() || i.type().id() == ID_c_bool);
  
  typecast_exprt eq(i,bool_typet());

  string_exprt true_string = string_constant("true",char_width,char_type);
  string_exprt false_string = string_constant("false",char_width,char_type);

  axioms.emplace_back(eq, res.same_length(true_string));
  symbol_exprt qvar = fresh_univ_index("QA_equal_true");
  axioms.push_back
    (string_constraintt(eq,equal_exprt(res[qvar],true_string[qvar])
			).forall(qvar,true_string.length()));

  axioms.emplace_back(not_exprt(eq), res.same_length(false_string));
  symbol_exprt qvar1 = fresh_univ_index("QA_equal_false");
  axioms.push_back
    (string_constraintt(not_exprt(eq),equal_exprt(res[qvar1],false_string[qvar1])
			).forall(qvar,false_string.length()));

  return res;
}


string_exprt string_constraint_generatort::of_int
(const exprt &i, size_t max_size)
{
  string_exprt res(get_char_type());
  typet type = i.type();
  assert(type.id() == ID_signedbv);
  size_t width = to_bitvector_type(type).get_width();
  exprt ten = constant_signed(10,width);
  exprt zero_char = constant_char('0'); 
  exprt nine_char = constant_char('9'); 
  exprt minus_char = constant_char('-');

  axioms.emplace_back(and_exprt(res.strictly_longer(refined_string_typet::index_zero()),
				res.shorter(refined_string_typet::index_of_int(max_size))));

  exprt chr = res[0];
  exprt starts_with_minus = equal_exprt(chr,minus_char);
  exprt starts_with_digit = and_exprt
    (binary_relation_exprt(chr,ID_ge,zero_char),
     binary_relation_exprt(chr,ID_le,nine_char));
  axioms.emplace_back(or_exprt(starts_with_digit,starts_with_minus));

  for(size_t size=1; size<=max_size;size++) 
    {
      exprt sum = constant_signed(0,width);
      exprt all_numbers = true_exprt();
      chr = res[0];
      exprt first_value = typecast_exprt(minus_exprt(chr,zero_char),type);
      
      for(size_t j=1; j<size; j++) 
	{
	  chr = res[j];
	  sum = plus_exprt(mult_exprt(sum,ten),typecast_exprt(minus_exprt(chr,zero_char),type));
	  first_value = mult_exprt(first_value,ten);
	  all_numbers = and_exprt(all_numbers,and_exprt
				  (binary_relation_exprt(chr,ID_ge,zero_char),
				   binary_relation_exprt(chr,ID_le,nine_char)));
	}

      equal_exprt premise = res.has_length(size);
      axioms.emplace_back(and_exprt(premise,starts_with_digit),
			  and_exprt(equal_exprt(i,plus_exprt(sum,first_value)),
				    all_numbers));
      
      axioms.emplace_back(and_exprt(premise,starts_with_minus),
			  and_exprt(equal_exprt(i,unary_minus_exprt(sum)),
				    all_numbers));
      //disallow 0s at the beggining
      if(size>1) 
	{
	  axioms.emplace_back(and_exprt(premise,starts_with_digit),
			      not_exprt(equal_exprt(res[refined_string_typet::index_zero()],zero_char)));
	  axioms.emplace_back(and_exprt(premise,starts_with_minus),
			      not_exprt(equal_exprt(res[refined_string_typet::index_of_int(1)],zero_char)));
	}

      //we have to be careful when exceeding the maximal size of integers
      // Warning this should be different depending on max size
      if(size == max_size)
	{
	  exprt smallest_with_10_digits = constant_signed(1000000000,width);
	  axioms.emplace_back(premise,binary_relation_exprt(i,ID_ge,smallest_with_10_digits));
	}
    }
  return res;
}


exprt string_constraint_generatort::int_of_hex_char(exprt chr, unsigned char_width, typet char_type) 
{
  exprt zero_char = constant_char(48);
  exprt nine_char = constant_char(57);
  exprt a_char = constant_char(0x61);
  return if_exprt(binary_relation_exprt(chr,ID_gt,nine_char),
		  minus_exprt(chr,constant_char(0x61 - 10)),
		  minus_exprt(chr,zero_char));
}


string_exprt string_constraint_generatort::of_int_hex(const exprt &i)
{
  string_exprt res(get_char_type());
  typet type = i.type();
  assert(type.id() == ID_signedbv);
  size_t width = to_bitvector_type(type).get_width();
  exprt sixteen = constant_signed(16,width);
  exprt minus_char = constant_char(45);
  exprt zero_char = constant_char(48);
  exprt nine_char = constant_char(57);
  exprt a_char = constant_char(0x61);
  exprt f_char = constant_char(0x66);

  size_t max_size = 8;
  axioms.emplace_back(and_exprt(res.strictly_longer(0),
				res.shorter(max_size)));

  for(size_t size=1; size<=max_size;size++)
    {
      exprt sum = constant_signed(0,width);
      exprt all_numbers = true_exprt();
      exprt chr = res[0];

      for(size_t j=0; j<size; j++)
	{
	  chr = res[j];
	  sum = plus_exprt(mult_exprt(sum,sixteen),typecast_exprt(int_of_hex_char(chr,get_char_width(),get_char_type()),type));
	  all_numbers = and_exprt
	    (all_numbers,
	     or_exprt(and_exprt
		      (binary_relation_exprt(chr,ID_ge,zero_char),
		       binary_relation_exprt(chr,ID_le,nine_char)),
		      and_exprt
		      (binary_relation_exprt(chr,ID_ge,a_char),
		       binary_relation_exprt(chr,ID_le,f_char))));
	}
      
      equal_exprt premise(res.has_length(size));
      axioms.emplace_back(premise, and_exprt(equal_exprt(i,sum),all_numbers));
      
      //disallow 0s at the beggining
      if(size>1) 
	axioms.emplace_back(premise, not_exprt(equal_exprt(res[0],zero_char)));
    }
  return res;
}

string_exprt string_constraint_generatort::of_int_hex
(const function_application_exprt &f)
{ return of_int_hex(args(f,1)[0]); }

string_exprt string_constraint_generatort::of_char
(const function_application_exprt &f)
{ return of_char(args(f,1)[0]); }

string_exprt string_constraint_generatort::of_char(const exprt &c)
{
  string_exprt res(get_char_type());
  and_exprt lemma(equal_exprt(res[0], c), res.has_length(1));
  axioms.push_back(lemma);
  return res;
}


string_exprt string_constraint_generatort::code_point(const exprt &code_point)
{
  string_exprt res(get_char_type());
  typet type = code_point.type();
  assert(type.id() == ID_signedbv);
  size_t width = to_bitvector_type(type).get_width();
  binary_relation_exprt small(code_point,ID_lt,constant_signed(0x010000,width));
  axioms.emplace_back(small, res.has_length(1));
  axioms.emplace_back(not_exprt(small),res.has_length(2));
  axioms.emplace_back(small,equal_exprt(res[0],typecast_exprt(code_point,get_char_type())));

  axioms.emplace_back(not_exprt(small),
		      equal_exprt
		      (res[0],
		       typecast_exprt
		       (plus_exprt(constant_signed(0xD800,width),
				   div_exprt(minus_exprt(code_point,constant_signed(0x010000,width)),constant_signed(0x0400,width))),
			get_char_type())));
  axioms.emplace_back(not_exprt(small),
		      equal_exprt
		      (res[1],
		       typecast_exprt
		       (plus_exprt(constant_signed(0xDC00,width),
				   mod_exprt(code_point,constant_signed(0x0400,width))),
			get_char_type())));
  return res;
}


string_exprt string_constraint_generatort::string_char_set
(const function_application_exprt &f)
{
  string_exprt res(get_char_type());
  string_exprt str = string_of_expr(args(f,3)[0]);
  //symbol_exprt c = fresh_symbol("char", refined_string_typet::get_char_type(args[0]));
  //axioms.emplace_back(equal_exprt(c,args(f,3)[2]));
  with_exprt sarrnew(str.content(), args(f,3)[1], args(f,3)[2]);
  implies_exprt lemma(binary_relation_exprt(args(f,3)[1], ID_lt, str.length()),
                      and_exprt(equal_exprt(res.content(), sarrnew),
                                res.same_length(str)));
  axioms.push_back(lemma);
  return res;
}

string_exprt string_constraint_generatort::string_replace
(const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,3)[0]);
  exprt oldChar = args(f,3)[1];
  exprt newChar = args(f,3)[2];
  string_exprt res(get_char_type());

  axioms.emplace_back(res.same_length(str));
  symbol_exprt qvar = fresh_univ_index("QA_replace");
  axioms.push_back
    (string_constraintt
     (and_exprt
      (implies_exprt(equal_exprt(str[qvar],oldChar),equal_exprt(res[qvar],newChar)),
       implies_exprt(not_exprt(equal_exprt(str[qvar],oldChar)),
		     equal_exprt(res[qvar],str[qvar]))
       )
      ).forall(qvar,res.length()));
  return res;
}

string_exprt string_constraint_generatort::string_delete_char_at
(const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,2)[0]);
  exprt index_one = refined_string_typet::index_of_int(1);
  return string_delete(str,args(f,2)[1],plus_exprt(args(f,2)[1],index_one));
}

string_exprt string_constraint_generatort::string_delete
(const string_exprt &str, const exprt & start, const exprt & end)
{
  assert(start.type() == refined_string_typet::index_type());
  assert(end.type() == refined_string_typet::index_type());
  string_exprt str1 = string_substring(str,refined_string_typet::index_zero(),start);
  string_exprt str2 = string_substring(str,end,str.length());
  return string_concat(str1,str2);
}

string_exprt string_constraint_generatort::string_delete
(const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,3)[0]);
  return string_delete(str,args(f,3)[1],args(f,3)[2]);
}


string_exprt string_constraint_generatort::string_concat_int
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,2)[0]);
  string_exprt s2 = of_int(args(f,2)[1],10);
  return string_concat(s1,s2);
}

string_exprt string_constraint_generatort::string_concat_long
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,2)[0]);
  string_exprt s2 = of_int(args(f,2)[1],30);
  return string_concat(s1,s2);
}

string_exprt string_constraint_generatort::string_concat_bool
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,2)[0]);
  string_exprt s2 = of_bool(args(f,2)[1]);
  return string_concat(s1,s2);
}

string_exprt string_constraint_generatort::string_concat_char
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,2)[0]);
  string_exprt s2 = of_char(args(f,2)[1]);
  return string_concat(s1,s2);
}

string_exprt string_constraint_generatort::string_concat_double
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,2)[0]);
  string_exprt s2 = of_float(args(f,2)[1],30);
  return string_concat(s1,s2);
}

string_exprt string_constraint_generatort::string_concat_float
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,2)[0]);
  string_exprt s2 = of_float(args(f,2)[1],10);
  return string_concat(s1,s2);
}

string_exprt string_constraint_generatort::string_concat_code_point
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,2)[0]);
  string_exprt s2 = code_point(args(f,2)[1]);
  return string_concat(s1,s2);
}

string_exprt string_constraint_generatort::string_insert
(const string_exprt & s1, const string_exprt & s2, const exprt & offset)
{
  assert(offset.type() == refined_string_typet::index_type());
  string_exprt pref = string_substring(s1,refined_string_typet::index_zero(),offset);
  string_exprt suf = string_substring(s1,offset,s1.length());
  string_exprt concat1 = string_concat(pref,s2);
  return string_concat(concat1,suf);
}

string_exprt string_constraint_generatort::string_insert
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,3)[0]);
  string_exprt s2 = string_of_expr(args(f,3)[2]); 
  return string_insert(s1, s2, args(f,3)[1]);
}

string_exprt string_constraint_generatort::string_insert_int
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,3)[0]);
  string_exprt s2 = of_int(args(f,3)[2],10);
  return string_insert(s1,s2,args(f,3)[1]);
}

string_exprt string_constraint_generatort::string_insert_long
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,3)[0]);
  string_exprt s2 = of_int(args(f,3)[2],30);
  return string_insert(s1,s2,args(f,3)[1]);
}

string_exprt string_constraint_generatort::string_insert_bool
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,3)[0]);
  string_exprt s2 = of_bool(args(f,3)[2]);
  return string_insert(s1,s2,args(f,3)[1]);
}

string_exprt string_constraint_generatort::string_insert_char
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,3)[0]);
  string_exprt s2 = of_char(args(f,3)[2]);
  return string_insert(s1,s2,args(f,3)[1]);
}

string_exprt string_constraint_generatort::string_insert_double
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,3)[0]);
  string_exprt s2 = of_float(args(f,3)[2]);
  return string_insert(s1,s2,args(f,3)[1]);
}

string_exprt string_constraint_generatort::string_insert_float
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,3)[0]);
  string_exprt s2 = of_float(args(f,3)[2]);
  return string_insert(s1,s2,args(f,3)[1]);
}


exprt string_constraint_generatort::string_equal
(const function_application_exprt &f)
 {
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);
  symbol_exprt eq = fresh_boolean("equal");
  typecast_exprt tc_eq(eq,f.type());

  string_exprt s1 = string_of_expr(args(f,2)[0]);
  string_exprt s2 = string_of_expr(args(f,2)[1]);

  // We want to write:
  // eq <=> (s1.length = s2.length  && forall i < s1.length. s1[i] = s2[i])
  // We can't do it directly because of the universal quantification inside.
  // So we say instead the three following:
  // eq => s1.length = s2.length
  // forall i < s1.length. eq => s1[i] = s2[i]
  // !eq => s1.length != s2.length || (witness < s1.length && s1[witness] != s2[witness])

  symbol_exprt witness = fresh_exist_index("witness_unequal");
  symbol_exprt qvar = fresh_univ_index("QA_equal");

  axioms.emplace_back(eq, s1.same_length(s2));
  axioms.push_back
    (string_constraintt(eq,equal_exprt(s1[qvar],s2[qvar])
			).forall(qvar,s1.length()));

  axioms.emplace_back
    (not_exprt(eq),
     or_exprt(notequal_exprt(s1.length(), s2.length()),
	      string_constraintt(notequal_exprt(s1[witness],s2[witness])).exists(witness,s1.length())));

  return tc_eq;
}

exprt character_equals_ignore_case
(exprt char1, exprt char2, exprt char_a, exprt char_A, exprt char_Z) 
{
  exprt is_upper_case_1 = and_exprt(binary_relation_exprt(char_A,ID_le,char1),
				  binary_relation_exprt(char1,ID_le,char_Z));
  exprt is_upper_case_2 = and_exprt(binary_relation_exprt(char_A,ID_le,char2),
				  binary_relation_exprt(char2,ID_le,char_Z));
  return or_exprt(or_exprt(equal_exprt(char1,char2),
			   and_exprt(is_upper_case_1, equal_exprt(minus_exprt(plus_exprt(char_a,char1),char_A),char2))),
		  and_exprt(is_upper_case_2, equal_exprt(minus_exprt(plus_exprt(char_a,char2),char_A),char1)));
}

exprt string_constraint_generatort::string_equals_ignore_case
(const function_application_exprt &f) 
{
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);
  
  symbol_exprt eq = fresh_boolean("equal_ignore_case");
  typecast_exprt tc_eq(eq,f.type());

  check_char_type(f); // is this necessary?

  exprt char_a = constant_char(97);
  exprt char_A = constant_char(65);
  exprt char_Z = constant_char(90);
  string_exprt s1 = string_of_expr(args(f,2)[0]);
  string_exprt s2 = string_of_expr(args(f,2)[1]);
  symbol_exprt witness = fresh_exist_index("witness_unequal_ignore_case");
  symbol_exprt qvar = fresh_univ_index("QA_equal_ignore_case");

  axioms.emplace_back(eq, s1.same_length(s2));

  axioms.push_back
    (string_constraintt(eq,character_equals_ignore_case(s1[qvar],s2[qvar],char_a,char_A,char_Z)
			).forall(qvar,s1.length()));

  axioms.emplace_back
    (not_exprt(eq),
     or_exprt(notequal_exprt(s1.length(), s2.length()),
	      string_constraintt(not_exprt(character_equals_ignore_case(s1[witness],s2[witness],char_a,char_A,char_Z))).exists(witness,s1.length())));
  
  return tc_eq;
}


exprt string_constraint_generatort::string_length
(const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,1)[0]);
  return str.length();
}

exprt string_constraint_generatort::string_data
(const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,3)[0]);
  exprt tab_data = args(f,3)[1];
  exprt data = args(f,3)[2];
  //axioms.push_back(equal_exprt(str.content(),data));
  //member_substitutions[data]=str;
  symbol_exprt qvar = fresh_univ_index("QA_string_data");
  // translating data[qvar]  to the correct expression
  // which is (signed int)byte_extract_little_endian(tab?data?, (2l*qvar) + POINTER_OFFSET(byte_extract_little_endian(tab.data, 0l, unsigned short int *)), unsigned short int)
  exprt char_in_tab =  typecast_exprt  
    (byte_extract_exprt(ID_byte_extract_little_endian,data,
			plus_exprt
			(mult_exprt(constant_signed(2,64),typecast_exprt(qvar,signedbv_typet(64))),
			 pointer_offset(byte_extract_exprt
					(ID_byte_extract_little_endian,
					 tab_data
					 ,constant_signed(0,64),pointer_typet(unsignedbv_typet(16))))),unsignedbv_typet(16)),
     get_char_type());

  string_constraintt eq(equal_exprt(str[qvar],char_in_tab));
  //string_constraintt eq(equal_exprt(constant_char('b'),char_in_tab));
  axioms.push_back(eq.forall(qvar,str.length()));

  exprt void_expr;
  void_expr.type() = void_typet();
  return void_expr;
}

exprt is_positive(const exprt & x)
{ return binary_relation_exprt(x, ID_ge, refined_string_typet::index_of_int(0)); }


exprt string_constraint_generatort::string_is_prefix(const string_exprt &prefix, const string_exprt &str, const exprt & offset)
{
  symbol_exprt isprefix = fresh_boolean("isprefix");
  axioms.emplace_back(isprefix, str.longer(plus_exprt(prefix.length(),offset)));

  // forall 0 <= witness < prefix.length. isprefix => s0[witness+offset] = s2[witness]
  symbol_exprt qvar = fresh_univ_index("QA_isprefix");
  axioms.push_back
    (string_constraintt(isprefix, equal_exprt(str[plus_exprt(qvar,offset)],prefix[qvar])
			).forall(qvar,prefix.length()));
	     
  symbol_exprt witness = fresh_exist_index("witness_not_isprefix");

  or_exprt s0_notpref_s1(not_exprt(str.longer(plus_exprt(prefix.length(),offset))),
			 and_exprt
			 (str.longer(plus_exprt(prefix.length(),offset)),
			  and_exprt(is_positive(witness),
				    and_exprt(prefix.strictly_longer(witness), 
					      notequal_exprt(str[plus_exprt(witness,offset)],prefix[witness])))));
		       
  axioms.emplace_back(implies_exprt(not_exprt(isprefix),s0_notpref_s1));
  return isprefix; 
}

exprt string_constraint_generatort::string_is_prefix
(const function_application_exprt &f, bool swap_arguments)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);
  string_exprt s0 = string_of_expr(args[swap_arguments?1:0]);
  string_exprt s1 = string_of_expr(args[swap_arguments?0:1]);
  exprt offset;
  if(args.size() == 2) offset = refined_string_typet::index_zero();
  else if (args.size() == 3) offset = args[2];
  return typecast_exprt(string_is_prefix(s0,s1,offset),f.type());
}

exprt string_constraint_generatort::string_is_empty
(const function_application_exprt &f)
{
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);
  symbol_exprt is_empty = fresh_boolean("is_empty");
  string_exprt s0 = string_of_expr(args(f,1)[0]);
  axioms.emplace_back(implies_exprt(is_empty, s0.has_length(0)));
  axioms.emplace_back(implies_exprt(s0.has_length(0),is_empty));
  return typecast_exprt(is_empty,f.type());

}

exprt string_constraint_generatort::string_is_suffix
(const function_application_exprt &f, bool swap_arguments)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string issuffix?
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);

  symbol_exprt issuffix = fresh_boolean("issuffix");
  typecast_exprt tc_issuffix(issuffix,f.type());
  string_exprt s0 = string_of_expr(args[swap_arguments?1:0]);
  string_exprt s1 = string_of_expr(args[swap_arguments?0:1]);

  // issufix(s1,s0) => s0.length >= s1.length
  // && forall witness < s1.length. 
  //     issufix => s1[witness] = s0[witness + s0.length - s1.length]
  // && !issuffix => s1.length > s0.length 
  //       || (s1.length > witness && s1[witness] != s0[witness + s0.length - s1.length]

  axioms.emplace_back(implies_exprt(issuffix, s1.longer(s0)));

  symbol_exprt qvar = fresh_univ_index("QA_suffix");
  exprt qvar_shifted = plus_exprt(qvar, 
				  minus_exprt(s1.length(), s0.length()));
  axioms.push_back
    (string_constraintt(issuffix, equal_exprt(s0[qvar],s1[qvar_shifted])
			).forall(qvar,s0.length()));

  symbol_exprt witness = fresh_exist_index("witness_not_suffix");

  exprt shifted = plus_exprt(witness, 
			     minus_exprt(s1.length(), s0.length()));

  implies_exprt lemma2(not_exprt(issuffix),
		       and_exprt(is_positive(witness),
				 or_exprt(s0.strictly_longer(s1),
					  and_exprt(s0.strictly_longer(witness), 
						    notequal_exprt(s0[witness],s1[shifted])))));

  axioms.emplace_back(lemma2);

  return tc_issuffix;
}


exprt string_constraint_generatort::string_contains
( const function_application_exprt &f)
{
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);
  symbol_exprt contains = fresh_boolean("contains");
  typecast_exprt tc_contains(contains,f.type());
  string_exprt s0 = string_of_expr(args(f,2)[0]);
  string_exprt s1 = string_of_expr(args(f,2)[1]);

  // contains => s0.length >= s1.length
  // && startpos <= s0.length - s1.length
  // && forall qvar < s1.length.
  //     contains => s1[qvar] = s0[startpos + qvar]
  // !contains => s1.length > s0.length 
  //       || (forall startpos <= s0.length - s1.length. 
  //             exists witness < s1.length && s1[witness] != s0[witness + startpos]

  axioms.emplace_back(implies_exprt(contains, s0.longer(s1)));
  symbol_exprt startpos = fresh_exist_index("startpos_contains");
  axioms.emplace_back(
		      and_exprt(is_positive(startpos),binary_relation_exprt(startpos, ID_le, minus_exprt(s0.length(),s1.length()))));

  symbol_exprt qvar = fresh_univ_index("QA_contains");
  exprt qvar_shifted = plus_exprt(qvar, startpos);
  axioms.push_back
    (string_constraintt(contains,equal_exprt(s1[qvar],s0[qvar_shifted])
			).forall(qvar,s1.length()));

  // We rewrite the axiom for !contains as:
  // forall startpos <= |s0| - |s1|.  (!contains && |s0| >= |s1| )
  //      ==> exists witness < |s1|. s1[witness] != s0[startpos+witness]
  axioms.push_back
    (string_constraintt::not_contains
     (refined_string_typet::index_zero(),plus_exprt(refined_string_typet::index_of_int(1),minus_exprt(s0.length(),s1.length())), 
      and_exprt(not_exprt(contains),s0.longer(s1)),refined_string_typet::index_zero(),s1.length(),s0,s1));

  return tc_contains;
}


exprt string_constraint_generatort::string_hash_code(const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,1)[0]);
  typet return_type = f.type();

  // initialisation of the missing pool variable
  std::map<irep_idt, string_exprt>::iterator it;
  for(it = symbol_to_string.begin(); it != symbol_to_string.end(); it++) 
    if(hash.find(it->second) == hash.end())
      hash[it->second] = string_exprt::fresh_symbol("hash", return_type);

  // for each string s. 
  //    hash(str) = hash(s) || |str| != |s| || (|str| == |s| && exists i < |s|. s[i] != str[i])

  // WARNING: the specification may be incomplete 
  for(it = symbol_to_string.begin(); it != symbol_to_string.end(); it++) {
    symbol_exprt i = fresh_exist_index("index_hash");
    axioms.emplace_back
      (or_exprt
       (equal_exprt(hash[it->second],hash[str]),
	or_exprt
	(not_exprt(equal_exprt(it->second.length(),str.length())),
	 and_exprt(equal_exprt(it->second.length(),str.length()),
		   and_exprt
		   (not_exprt(equal_exprt(str[i],it->second[i])),
		    and_exprt(str.strictly_longer(i),is_positive(i))
		    )))));
  }
  return hash[str];
}

exprt string_constraint_generatort::string_index_of
(const string_exprt &str, const exprt & c, const exprt & from_index)
{
  symbol_exprt index = fresh_exist_index("index_of");
  symbol_exprt contains = fresh_boolean("contains_in_index_of");

  // from_index <= i < |s| && (i = -1 <=> !contains) && (contains => i >= from_index && s[i] = c)
  // && forall n. from_index <= n < i => s[n] != c 
  
  axioms.push_back(string_constraintt
		   (equal_exprt(index,refined_string_typet::index_of_int(-1)),not_exprt(contains)
		    ).exists(index,refined_string_typet::index_of_int(-1),str.length()));
  axioms.emplace_back(not_exprt(contains),equal_exprt(index,refined_string_typet::index_of_int(-1)));
  axioms.emplace_back(contains,and_exprt(binary_relation_exprt(from_index,ID_le,index),equal_exprt(str[index],c)));

  symbol_exprt n = fresh_univ_index("QA_index_of");
  axioms.push_back(string_constraintt
		   (contains,not_exprt(equal_exprt(str[n],c))).forall(n,from_index,index));

  symbol_exprt m = fresh_univ_index("QA_index_of");

  axioms.push_back(string_constraintt
		   (not_exprt(contains),not_exprt(equal_exprt(str[m],c))
		    ).forall(m,from_index,str.length()));

  return index;
}

exprt string_constraint_generatort::string_index_of_string(const string_exprt &str, const string_exprt & substring, const exprt & from_index)
{
  symbol_exprt offset = fresh_exist_index("index_of");
  symbol_exprt contains = fresh_boolean("contains_substring");
  axioms.emplace_back(contains, and_exprt
		      (str.longer(plus_exprt(substring.length(),offset)),
		       binary_relation_exprt(offset,ID_ge,from_index)));
  axioms.emplace_back(not_exprt(contains), equal_exprt(offset,refined_string_typet::index_of_int(-1)));
  
  // forall 0 <= witness < substring.length. contains => str[witness+offset] = substring[witness]
  symbol_exprt qvar = fresh_univ_index("QA_index_of_string");
  axioms.push_back
    (string_constraintt(contains, equal_exprt(str[plus_exprt(qvar,offset)],substring[qvar])
			).forall(qvar,substring.length()));
	     
  return offset; 
}

exprt string_constraint_generatort::string_last_index_of_string(const string_exprt &str, const string_exprt & substring, const exprt & from_index)
{
  symbol_exprt offset = fresh_exist_index("index_of");
  symbol_exprt contains = fresh_boolean("contains_substring");
  axioms.emplace_back(contains, and_exprt
		      (str.longer(plus_exprt(substring.length(),offset)),
		       binary_relation_exprt(offset,ID_le,from_index)));
  axioms.emplace_back(not_exprt(contains), equal_exprt(offset,refined_string_typet::index_of_int(-1)));
  
  // forall 0 <= witness < substring.length. contains => str[witness+offset] = substring[witness]
  symbol_exprt qvar = fresh_univ_index("QA_index_of_string");
  axioms.push_back
    (string_constraintt(contains, equal_exprt(str[plus_exprt(qvar,offset)],substring[qvar])
			).forall(qvar,substring.length()));
  
  return offset; 
}


exprt string_constraint_generatort::string_index_of
( const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(f.type() == refined_string_typet::index_type());
  string_exprt str = string_of_expr(args[0]);
  exprt c = args[1];
  exprt from_index;

  if(args.size() == 2) from_index = refined_string_typet::index_zero();
  else if (args.size() == 3) from_index = args[2];
  else assert(false);

  if(refined_string_typet::is_java_string_type(c.type()))
    {
      string_exprt sub = string_of_expr(c);
      return string_index_of_string(str,sub,from_index);    
    } 
  else
    return string_index_of(str,typecast_exprt(c,get_char_type()),from_index);    
}

exprt string_constraint_generatort::string_last_index_of
(const string_exprt &str, const exprt & c, const exprt & from_index) 
{
  symbol_exprt index = fresh_exist_index("last_index_of");
  symbol_exprt contains = fresh_boolean("contains_in_last_index_of");

  // -1 <= i <= from_index && (i = -1 <=> !contains) && (contains => i <= from_index && s[i] = c)
  // && forall n. i <= n <= from_index => s[n] != c 

  exprt from_index_plus_one = plus_exprt(from_index,refined_string_typet::index_of_int(1));
  axioms.push_back(string_constraintt(equal_exprt(index,refined_string_typet::index_of_int(-1)),not_exprt(contains)).exists(index,refined_string_typet::index_of_int(-1),from_index_plus_one));
  axioms.emplace_back(not_exprt(contains),equal_exprt(index,refined_string_typet::index_of_int(-1)));
  axioms.emplace_back(contains,and_exprt(is_positive(index),and_exprt(binary_relation_exprt(from_index,ID_ge,index),equal_exprt(str[index],c))));
  
  symbol_exprt n = fresh_univ_index("QA_last_index_of");
  axioms.push_back(string_constraintt(contains,not_exprt(equal_exprt(str[n],c))).forall(n,plus_exprt(index,refined_string_typet::index_of_int(1)),from_index_plus_one));

  symbol_exprt m = fresh_univ_index("QA_last_index_of");
  axioms.push_back(string_constraintt(not_exprt(contains),not_exprt(equal_exprt(str[m],c))).forall(m,from_index_plus_one));

  return index;
}

exprt string_constraint_generatort::string_last_index_of
( const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(f.type() == refined_string_typet::index_type());
  string_exprt str = string_of_expr(args[0]);
  exprt c = args[1];
  exprt from_index;

  if(args.size() == 2) from_index = minus_exprt(str.length(),refined_string_typet::index_of_int(1));
  else if (args.size() == 3) from_index = args[2];
  else assert(false);

  if(refined_string_typet::is_java_string_type(c.type()))
    {
      string_exprt sub = string_of_expr(c);
      return string_last_index_of_string(str,sub,from_index);    
    } 
  else
    return string_last_index_of(str,typecast_exprt(c,get_char_type()),from_index);
}

exprt string_constraint_generatort::char_literal
( const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); // there should be exactly 1 argument to char literal

  const exprt &arg = args[0];
  // for C programs argument to char literal should be one string constant of size one
  if(arg.operands().size() == 1 &&
     arg.op0().operands().size() == 1 &&
     arg.op0().op0().operands().size() == 2 &&
     arg.op0().op0().op0().id() == ID_string_constant)
  {
    const string_constantt s = to_string_constant(arg.op0().op0().op0());
    irep_idt sval = s.get_value();
    assert(sval.size() == 1); 
    
    std::string binary=integer2binary(unsigned(sval[0]), STRING_SOLVER_CHAR_WIDTH);
    
    return constant_exprt(binary, get_char_type());
  }
  else
    {
      throw "convert_char_literal unimplemented";
    }
    
}


exprt string_constraint_generatort::string_char_at
( const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,2)[0]);
  symbol_exprt char_sym = string_exprt::fresh_symbol("char",get_char_type());
  axioms.emplace_back(equal_exprt(char_sym,str[args(f,2)[1]]));
  return char_sym;
}

exprt string_constraint_generatort::string_parse_int
(const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,1)[0]);
  typet type = f.type();
  symbol_exprt i = string_exprt::fresh_symbol("parsed_int",type);

  exprt zero_char = constant_char(48);
  exprt minus_char = constant_char(45);
  exprt plus_char = constant_char(43);
  assert(type.id() == ID_signedbv);
  size_t width = to_bitvector_type(type).get_width();
  constant_exprt ten(integer2binary(10,width),type);
  
  exprt chr = str[0];
  exprt starts_with_minus = equal_exprt(chr,minus_char);
  exprt starts_with_plus = equal_exprt(chr,plus_char);
  exprt starts_with_digit = binary_relation_exprt(chr,ID_ge,zero_char); 
  
  for(unsigned size=1; size<=10;size++) 
    {
      exprt sum = constant_exprt(integer2binary(0,width),type);
      exprt first_value = typecast_exprt(minus_exprt(chr,zero_char),type);
      
      for(unsigned j=1; j<size; j++)
	{
	  sum = plus_exprt(mult_exprt(sum,ten),typecast_exprt(minus_exprt(str[j],zero_char),type));
	  first_value = mult_exprt(first_value,ten);
	}
      
      equal_exprt premise = str.has_length(size);
      axioms.emplace_back(and_exprt(premise,starts_with_digit),
			  equal_exprt(i,plus_exprt(sum,first_value)));
      axioms.emplace_back(and_exprt(premise,starts_with_plus),
			  equal_exprt(i,sum));
      axioms.emplace_back(and_exprt(premise,starts_with_minus),
			  equal_exprt(i,unary_minus_exprt(sum)));
    }
  return i;
}


exprt string_constraint_generatort::is_high_surrogate(const exprt & chr) 
{
  return and_exprt
    (binary_relation_exprt(chr,ID_ge,constant_char(0xD800)),
     binary_relation_exprt(chr,ID_le,constant_char(0xDBFF)));
}

exprt string_constraint_generatort::is_low_surrogate(const exprt & chr)
{
  return and_exprt
    (binary_relation_exprt(chr,ID_ge,constant_char(0xDC00)),
     binary_relation_exprt(chr,ID_le,constant_char(0xDFFF)));
}

exprt string_constraint_generatort::string_code_point_at
( const function_application_exprt &f)
{
  typet return_type = f.type();
  string_exprt str = string_of_expr(args(f,2)[0]);
  exprt pos = args(f,2)[1];
  symbol_exprt result = string_exprt::fresh_symbol("char",return_type);
  assert(return_type.id() == ID_signedbv);
  size_t width = to_bitvector_type(return_type).get_width();

  exprt char1_as_int = typecast_exprt(str[pos],return_type);
  exprt char2_as_int = typecast_exprt(str[plus_exprt(pos,refined_string_typet::index_of_int(1))],return_type);
  
  exprt pair_value = 
    plus_exprt
    (constant_signed(0x010000,width),
     (plus_exprt
      (mult_exprt
       (mod_exprt(char1_as_int,constant_signed(0x0800,width)),
	constant_signed(0x0400,width)),
       mod_exprt(char2_as_int,constant_signed(0x0400,width)))));
  
  exprt return_pair = and_exprt(is_high_surrogate(str[pos]),
				is_low_surrogate(str[plus_exprt(pos,refined_string_typet::index_of_int(1))]));

  axioms.emplace_back(return_pair,equal_exprt(result,pair_value));
  axioms.emplace_back(not_exprt(return_pair), equal_exprt(result,char1_as_int));
  return result;
}

exprt string_constraint_generatort::string_code_point_before
( const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2);
  typet return_type = f.type();
  symbol_exprt result = string_exprt::fresh_symbol("char",return_type);
  string_exprt str = string_of_expr(args[0]);

  exprt char1 = str[minus_exprt(args[1],refined_string_typet::index_of_int(2))];
  exprt char1_as_int = typecast_exprt(char1,return_type);
  exprt char2 = str[minus_exprt(args[1],refined_string_typet::index_of_int(1))];
  exprt char2_as_int = typecast_exprt(char2,return_type);

  assert(return_type.id() == ID_signedbv);
  size_t width = to_bitvector_type(return_type).get_width();

  exprt pair_value = 
    plus_exprt
    (constant_signed(0x010000,width),
     (plus_exprt
      (mult_exprt
       (mod_exprt(char1_as_int,constant_signed(0x0800,width)),
	constant_signed(0x0400,width)),
       mod_exprt(char2_as_int,constant_signed(0x0400,width)))));
  
  exprt return_pair = and_exprt(is_high_surrogate(char1),is_low_surrogate(char2));

  axioms.emplace_back(return_pair,equal_exprt(result,pair_value));
  axioms.emplace_back(not_exprt(return_pair),
			     equal_exprt(result,char2_as_int));
  return result;
}

exprt string_constraint_generatort::string_code_point_count
( const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,3)[0]);
  exprt begin = args(f,3)[1];
  exprt end = args(f,3)[2];
  typet return_type = f.type();
  symbol_exprt result = string_exprt::fresh_symbol("code_point_count",return_type);
  exprt length = minus_exprt(end,begin);
  axioms.emplace_back(binary_relation_exprt(result,ID_le,length));
  axioms.emplace_back(binary_relation_exprt(result,ID_ge,div_exprt(length,refined_string_typet::index_of_int(2))));

  return result;
}

exprt string_constraint_generatort::string_offset_by_code_point
( const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,3)[0]);
  exprt index = args(f,3)[1];
  exprt offset = args(f,3)[2];
  typet return_type = f.type();
  symbol_exprt result = string_exprt::fresh_symbol("offset_by_code_point",return_type);
  exprt minimum = plus_exprt(index,plus_exprt(index,offset));
  exprt maximum = plus_exprt(index,plus_exprt(index,mult_exprt(offset,refined_string_typet::index_of_int(2))));
  axioms.emplace_back(binary_relation_exprt(result,ID_le,maximum));
  axioms.emplace_back(binary_relation_exprt(result,ID_ge,minimum));

  return result;
}


exprt string_constraint_generatort::string_to_char_array
(const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,1)[0]);
  return str.content();
}


exprt string_constraint_generatort::string_compare_to
(const function_application_exprt &f)
{
  string_exprt s1 = string_of_expr(args(f,2)[0]);
  string_exprt s2 = string_of_expr(args(f,2)[1]);
  typet return_type = f.type();
  symbol_exprt res = string_exprt::fresh_symbol("compare_to",return_type);

  // In the lexicographic comparison, x is the first point where the two strings differ.
  // res == 0 => |s1| = |s2| && forall i < |s1|. s1[i] == s2[i]
  // res != 0 => 
  //   (|s1| <= |s2| && exists x < |s1|. res = s1[x] - s2[x] && forall i<x s1[i]=s2[i])
  //   || (|s1| >= |s2| && exists x < |s2|. res = s1[x] - s2[x] && forall i<x s1[i]=s2[i])
  //   || (|s1| < |s2| && res = |s1| - |s2| && forall i<|s1| s1[i]=s2[i])
  //   || (|s1| > |s2| && res = |s1| - |s2| && forall i<|s2| s1[i]=s2[i])
  
  // The second part can be rewriten as:
  // exists x. 
  // res != 0 ==> x> 0 &&
  // ((|s1| <= |s2| && x < |s1|) || (|s1| >= |s2| && x < |s2|) && res = s1[x] - s2[x] )
  // || (|s1| < |s2| && x = |s1|) || (|s1| > |s2| && x = |s2|) && res = |s1| - |s2|
  // && forall i < x. res != 0 => s1[i] = s2[i]

  assert(return_type.id() == ID_signedbv);
  size_t width = to_bitvector_type(return_type).get_width();

  symbol_exprt i = fresh_univ_index("QA_compare_to");
  equal_exprt res_null = equal_exprt(res,constant_signed(0,width));
  axioms.emplace_back(res_null, s1.same_length(s2));
  axioms.push_back(string_constraintt
		   (res_null,equal_exprt(s1[i],s2[i])).forall(i,s1.length()));

  symbol_exprt x = fresh_exist_index("index_compare_to");
  axioms.push_back
    (implies_exprt
     (not_exprt(res_null),
      and_exprt
      (binary_relation_exprt(x,ID_ge,constant_signed(0,width)),
       or_exprt
       (and_exprt
	(equal_exprt(res,typecast_exprt(minus_exprt(s1[x],s2[x]),return_type)),
	 or_exprt
	 (and_exprt(s1.shorter(s2),s1.strictly_longer(x)), 
	  and_exprt(s1.longer(s2),s2.strictly_longer(x)))),
	and_exprt
	(equal_exprt(res,typecast_exprt(minus_exprt(s1.length(),s2.length()),
					return_type)),
	 or_exprt
	 (and_exprt(s2.strictly_longer(s1),s1.has_length(x)), 
	  and_exprt(s1.strictly_longer(s2),s2.has_length(x))))))));

  axioms.push_back(string_constraintt
		   (not_exprt(res_null),equal_exprt(s1[i],s2[i])).forall(i,x));

  return res;
}

symbol_exprt string_constraint_generatort::string_intern(const function_application_exprt &f)
{
  string_exprt str = string_of_expr(args(f,1)[0]);
  typet return_type = f.type();

  // initialisation of the missing pool variable
  std::map<irep_idt, string_exprt>::iterator it;
  for(it = symbol_to_string.begin(); it != symbol_to_string.end(); it++) 
    if(pool.find(it->second) == pool.end())
      pool[it->second] = string_exprt::fresh_symbol("pool", return_type);

  // intern(str) = s_0 || s_1 || ...
  // for each string s. 
  //    intern(str) = intern(s) || |str| != |s| || (|str| == |s| && exists i < |s|. s[i] != str[i])
  
  //symbol_exprt intern = string_exprt::fresh_symbol("intern",return_type);

  exprt disj = false_exprt();
  for(it = symbol_to_string.begin(); it != symbol_to_string.end(); it++) 
    disj = or_exprt(disj, equal_exprt(pool[str], symbol_exprt(it->first,return_type)));
  
  axioms.emplace_back(disj);


  // WARNING: the specification may be incomplete or incorrect
  for(it = symbol_to_string.begin(); it != symbol_to_string.end(); it++) 
    if(it->second != str) {
      symbol_exprt i = fresh_exist_index("index_intern");
      axioms.emplace_back
	(or_exprt
	 (equal_exprt(pool[it->second],pool[str]),
	  or_exprt
	  (not_exprt(str.same_length(it->second)),
	   and_exprt(str.same_length(it->second),
		     and_exprt(not_exprt(equal_exprt(str[i],it->second[i])),
			       and_exprt(str.strictly_longer(i),is_positive(i)
					 ))))));
    }
			

  return pool[str];
}

// #include <iostream> for debugging

string_exprt string_constraint_generatort::string_format(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  unsignedbv_typet char_type = get_char_type();

  if(args.size() == 2) 
    {
      // Warning: this is not very clean:
      irep_idt literal = extract_java_string(to_symbol_expr(args[0].op1().op0().op0()));
      std::string format_string = id2string(literal);
      //std::cout << "string_exprt::of_string_format " << format_string << std::endl;
      size_t position = format_string.find_first_of('%');
      std::vector<string_exprt> strings;
      int arg_counter = 0;

      string_exprt begin = string_constant(format_string.substr(0,position),get_char_width(),char_type);
      strings.push_back(begin);
      //std::cout << "string_exprt::of_string_format : " << f.pretty() << std::endl;
      //typecast_exprt arg_tab(member_exprt(args[1].op0(),"data"),array_typet(java_type_from_string("Ljava/lang/Object;"),infinity_exprt(refined_string_typet::index_type())));
      member_exprt arg_tab(args[1].op0(),"data",array_typet(java_type_from_string("Ljava/lang/Object;"),infinity_exprt(refined_string_typet::index_type())));
      //std::cout << "string_exprt::arg_tab : " << arg_tab.type().pretty() << std::endl;

      while(position != std::string::npos) 
	{
	  switch(format_string[position+1]) {
	  case 'd' : 
	    {
	    index_exprt arg_object(arg_tab,refined_string_typet::index_of_int(arg_counter++)); 
	    typecast_exprt arg_int(arg_object, signedbv_typet(32));
	    symbol_exprt var_arg_int = string_exprt::fresh_symbol("format_arg_int", signedbv_typet(32));
	    axioms.push_back(equal_exprt(arg_int,var_arg_int));
	    axioms.push_back(equal_exprt(var_arg_int,refined_string_typet::index_of_int(12)));
	    string_exprt str = of_int(var_arg_int,10);
	    strings.push_back(str);
	    //    std::cout << "string format: position " << position << " int arg: " << arg_int.pretty() << std::endl;
	    break;
	    }

	  default:
	    {
	      //std::cout << "warning: unknown string format: " << format_string << std::endl;
	      break;
	    }
	  }
	  size_t new_position = format_string.find_first_of('%',position+2);
	  if(new_position != std::string::npos) {
	    string_exprt str = string_constant(format_string.substr(position+2,new_position),
					       get_char_width(),char_type);
	    strings.push_back(str);
	  }
	  position = new_position;
	}

      string_exprt * concatenation = &strings[0];
      unsigned i;
      for(i = 1; i < strings.size() - 1; i++)
	{
	  string_exprt str = string_concat(*concatenation,strings[i]);
	  concatenation = &str;
	}
      
      return string_concat(*concatenation,strings[i]);
    }
  else assert(false);
}

void string_constraint_generatort::string_of_expr(const symbol_exprt & sym, const exprt & str) 
{
  if(str.id()==ID_symbol) 
    assign_to_symbol(sym,string_of_symbol(to_symbol_expr(str)));
  else 
    assign_to_symbol(sym,string_of_expr(str));
}

/*

string_exprt string_constraint_generator::string_of_expr(const exprt & str) 
{
  //debug() << "string_constraint_generatort::string_of_expr of " << pretty_short(str) << eom;
  if(str.id()==ID_symbol) 
    return string_of_symbol(to_symbol_expr(str));
  else
    if (str.id() == ID_function_application &&
	starts_with(to_symbol_expr(to_function_application_expr(str).function()).get_identifier(),cprover_string_intern_func)) { 
      symbol_exprt sym1 = string_intern(to_function_application_expr(str));
      string_exprt s(refined_string_typet::java_char_type());
      assign_to_symbol(sym1,s);
      return s;
    }
    else
      return string_exprt::of_expr(str,symbol_to_string,axioms);
}
*/



/** -*- C++ -*- *****************************************************\

Module: Constraint generation from string function calls
        for the PASS algorithm (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint_generator.h>
#include <util/unicode.h>
#include <ansi-c/string_constant.h>

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

void string_constraint_generatort::check_char_type(const exprt & str) 
{
  if(language == C)
    assert(refined_string_typet::is_c_string_type(str.type()));
  else
    if(language == UNKNOWN)
      if(refined_string_typet::is_c_string_type(str.type()))
	language = C;
      else
	language = JAVA;

}

unsignedbv_typet get_char_type()
{ 
  if(language==C)
    return refined_string_typet::char_type();
  else if(language==JAVA) return refined_string_typet::java_char_type();
  else assert(false);
}

unsignedbv_typet get_char_width()
{ 
  if(language==C)
    return STRING_SOLVER_CHAR_WIDTH;
  else if(language==JAVA) return JAVA_STRING_SOLVER_CHAR_WIDTH;
  else assert(false);
}

string_exprt string_constraint_generatort::string_of_expr(const exprt & unrefined_string)
{
  unsignedbv_typet char_type;

  if(refined_string_typet::is_c_string_type(unrefined_string.type())) 
    char_type = refined_string_typet::char_type();
  else
    char_type = refined_string_typet::java_char_type();

  string_exprt s;
    
  switch(unrefined_string.id()) 
    { 
    case ID_function_application:
      s = of_function_application(to_function_application_expr(unrefined_string));
      else if(unrefined_string.id()==ID_symbol) 
	s = get_string_of_symbol(symbol_to_string,to_symbol_expr(unrefined_string));
      else if(unrefined_string.id()==ID_address_of) {
	assert(unrefined_string.op0().id()==ID_symbol);
	s = get_string_of_symbol(symbol_to_string,to_symbol_expr(unrefined_string.op0()));
      }
      else if(unrefined_string.id()==ID_if) 
	s.of_if(to_if_expr(unrefined_string),symbol_to_string,axioms);
      else if(unrefined_string.id()==ID_nondet_symbol || unrefined_string.id()==ID_struct) {
	// We ignore non deterministic symbols and struct
      }
    default:
    throw ("string_exprt of:\n" + unrefined_string.pretty() 
	   + "\nwhich is not a function application, a symbol or an if expression");
    }

  axioms.emplace_back(s >= refined_string_typet::index_zero());
  return s;
}



string_exprt string_constraint_generatort::of_if(const if_exprt &expr)
{
  assert(refined_string_typet::is_unrefined_string_type(expr.true_case().type()));
  string_exprt t = string_of_expr(expr.true_case());
  assert(refined_string_typet::is_unrefined_string_type(expr.false_case().type()));
  string_exprt f = string_of_expr(expr.false_case());

  axioms.emplace_back(expr.cond(),equal_exprt(length(),t.length()));
  symbol_exprt qvar = fresh_symbol("string_if_true",refined_string_typet::index_type());
  axioms.push_back(string_constraintt(expr.cond(),equal_exprt((*this)[qvar],t[qvar])).forall(qvar,t.length()));
  
  axioms.emplace_back(not_exprt(expr.cond()),equal_exprt(length(),f.length()));
  symbol_exprt qvar2 = fresh_symbol("string_if_false",refined_string_typet::index_type());
  axioms.push_back(string_constraintt(not_exprt(expr.cond()),equal_exprt((*this)[qvar2],f[qvar2])).forall(qvar2,f.length()));
}


string_exprt string_constraint_generatort::get_string_of_symbol(std::map<irep_idt, string_exprt> & symbol_to_string, const symbol_exprt & sym) {
  if(refined_string_typet::is_c_string_type(sym.type())) {
    irep_idt id = sym.get_identifier();
    std::map<irep_idt, string_exprt>::iterator f = symbol_to_string.find(id);
    if(f == symbol_to_string.end()) {
      symbol_to_string[id]= string_exprt(refined_string_typet::char_type());
      return symbol_to_string[id];
    } else return f->second;
  }  else { // otherwise we assume it is a java string
    irep_idt id = sym.get_identifier();
    std::map<irep_idt, string_exprt>::iterator f = symbol_to_string.find(id);
    if(f == symbol_to_string.end()) {
      symbol_to_string[id]= string_exprt(refined_string_typet::java_char_type());
      return symbol_to_string[id];
    } else return f->second;
  }

}

string_exprt string_constraint_generatort::string_of_symbol(const symbol_exprt & sym)
{
  if(refined_string_typet::is_java_string_type(sym.type()) 
     && starts_with(std::string(sym.get(ID_identifier).c_str()),"java::java.lang.String.Literal.")) 
    {
      assert(false); // is this branch used ?
      string_exprt s;
      s = generator.of_string_constant(string_exprt::extract_java_string(sym),JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
    return s;
  }
  else {
    return string_exprt::get_string_of_symbol(symbol_to_string,sym);
  }
}  


string_exprt string_constraint_generatort::function_application(const function_application_exprt & expr)
{
  const exprt &name = expr.function();

  if (name.id() == ID_symbol) {
    const irep_idt &id = to_symbol_expr(name).get_identifier();
    if (starts_with(id,cprover_string_literal_func)
	|| starts_with(id,cprover_string_concat_func)
	|| starts_with(id,cprover_string_substring_func)
	|| starts_with(id,cprover_string_char_set_func)) {
      string_exprt str = generator.make_string(expr);
      bvt bv = convert_bv(str);
      return bv;
    } else if (starts_with(id,cprover_char_literal_func)) {
      return char_literal(expr);
    } else if (starts_with(id,cprover_string_length_func)) {
      return generator.string_length(expr);
    } else if (starts_with(id,cprover_string_equal_func)) {
      return generator.string_equal(expr);
    } else if (starts_with(id,cprover_string_equals_ignore_case_func)) {
      return generator.string_equals_ignore_case(expr);
    } else if (starts_with(id,cprover_string_is_empty_func)) {
      return generator.string_is_empty(expr);
    } else if (starts_with(id,cprover_string_char_at_func)) {
      return generator.string_char_at(expr);
    } else if (starts_with(id,cprover_string_is_prefix_func)) {
      return generator.string_is_prefix(expr);
    } else if (starts_with(id,cprover_string_is_suffix_func)) {
      return generator.string_is_suffix(expr);
    } else if (starts_with(id,cprover_string_startswith_func)) {
      return generator.string_is_prefix(expr,true);
    } else if (starts_with(id,cprover_string_endswith_func)) {
      return generator.string_is_suffix(expr,true);
    } else if (starts_with(id,cprover_string_contains_func)) {
      return generator.string_contains(expr);
    } else if (starts_with(id,cprover_string_hash_code_func)) {
      return generator.string_hash_code(expr);
    } else if (starts_with(id,cprover_string_index_of_func)) {
      return generator.string_index_of(expr);
    } else if (starts_with(id,cprover_string_last_index_of_func)) {
      return generator.string_last_index_of(expr);
    } else if (starts_with(id,cprover_string_parse_int_func)) {
      return generator.string_parse_int(expr);
    } else if (starts_with(id,cprover_string_to_char_array_func)) {
      return generator.string_to_char_array(expr);
    } else if (starts_with(id,cprover_string_code_point_at_func)) {
      return generator.string_code_point_at(expr);
    } else if (starts_with(id,cprover_string_code_point_before_func)) {
      return generator.string_code_point_before(expr);
    } else if (starts_with(id,cprover_string_code_point_count_func)) {
      return generator.string_code_point_count(expr);
    } else if (starts_with(id,cprover_string_offset_by_code_point_func)) {
      return generator.string_offset_by_code_point(expr);
    } else if (starts_with(id,cprover_string_compare_to_func)) {
      return generator.string_compare_to(expr);
    } else if(starts_with(id,cprover_string_literal_func))
       return of_string_literal(expr,axioms);
    else if(starts_with(id,cprover_string_concat_func))
      return of_string_concat(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_concat_int_func))
      return of_string_concat_int(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_concat_long_func))
      return of_string_concat_long(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_concat_bool_func))
      return of_string_concat_bool(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_concat_char_func))
      return of_string_concat_char(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_concat_double_func))
      return of_string_concat_double(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_concat_float_func))
      return of_string_concat_float(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_concat_code_point_func))
      return of_string_concat_code_point(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_insert_func))
      return of_string_insert(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_insert_int_func))
      return of_string_insert_int(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_insert_long_func))
      return of_string_insert_long(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_insert_bool_func))
      return of_string_insert_bool(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_insert_char_func))
      return of_string_insert_char(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_insert_double_func))
      return of_string_insert_double(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_insert_float_func))
      return of_string_insert_float(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_substring_func))
      return of_string_substring(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_trim_func))
      return of_string_trim(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_to_lower_case_func))
      return of_string_to_lower_case(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_to_upper_case_func))
      return of_string_to_upper_case(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_char_set_func))
      return of_string_char_set(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_value_of_func))
      return of_string_value_of(expr,axioms);
    else if(starts_with(id,cprover_string_empty_string_func))
      return of_empty_string(expr,axioms);
    else if(starts_with(id,cprover_string_copy_func))
      return of_string_copy(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_of_int_func))
      return of_int(expr,axioms);
    else if(starts_with(id,cprover_string_of_int_hex_func))
      return of_int_hex(expr,axioms);
    else if(starts_with(id,cprover_string_of_float_func))
      return of_float(expr,axioms);
    else if(starts_with(id,cprover_string_of_double_func))
      return of_double(expr,axioms);
    else if(starts_with(id,cprover_string_of_long_func))
      return of_long(expr,axioms);
    else if(starts_with(id,cprover_string_of_bool_func))
      return of_bool(expr,axioms);
    else if(starts_with(id,cprover_string_of_char_func))
      return of_char(expr,axioms);
    else if(starts_with(id,cprover_string_set_length_func))
      return of_string_set_length(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_delete_func))
      return of_string_delete(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_delete_char_at_func))
      return of_string_delete_char_at(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_replace_func))
      return of_string_replace(expr,symbol_to_string,axioms);
    else if(starts_with(id,cprover_string_format_func))
      return of_string_format(expr,symbol_to_string,axioms);
    else {
      std::string msg("string_exprt::of_function_application: unknown symbol :");
      msg+=id.c_str();
      throw msg;
    }
  }
  throw "string_constraint_generator::function_application: not a string function";
}



irep_idt string_constraint_generatort::extract_java_string(const symbol_exprt & s){
  std::string tmp(s.get(ID_identifier).c_str());
  std::string value = tmp.substr(31);
  return irep_idt(value);
}

string_exprt string_constraint_generatort::of_string_constant(irep_idt sval, int char_width, unsignedbv_typet char_type, axiom_vect &axioms){

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
    equal_exprt lemma(index_exprt(content(), idx), c);
    axioms.emplace_back(lemma,true);
  }
  
  std::string s_length_binary = integer2binary(unsigned(utf16.size()),STRING_SOLVER_INDEX_WIDTH);
  exprt s_length = constant_exprt(s_length_binary, refined_string_typet::index_type());

  axioms.emplace_back(equal_exprt(length(),s_length));
}
				   
string_exprt string_constraint_generatort::of_empty_string(const function_application_exprt &f, axiom_vect & axioms)
{
  assert(f.arguments().size() == 0); 
  axioms.emplace_back(equal_exprt(length(),refined_string_typet::index_zero()));
}

string_exprt string_constraint_generatort::of_string_literal(const function_application_exprt &f, axiom_vect & axioms)
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

  of_string_constant(sval,char_width,char_type,axioms);
}


string_exprt string_constraint_generatort::of_string_concat(const string_exprt & s1, const string_exprt & s2, axiom_vect & axioms) {
  equal_exprt length_sum_lem(length(), plus_exprt(s1.length(), s2.length()));
  axioms.emplace_back(length_sum_lem);

  symbol_exprt idx = fresh_symbol("QA_index_concat",refined_string_typet::index_type());

  string_constraintt a1(equal_exprt(s1[idx],(*this)[idx]));
  axioms.push_back(a1.forall(idx, s1.length()));


  symbol_exprt idx2 = fresh_symbol("QA_index_concat2",refined_string_typet::index_type());

  string_constraintt a2(equal_exprt(s2[idx2],(*this)[plus_exprt(idx2,s1.length())]));
  axioms.push_back(a2.forall(idx2, s2.length()));
}

string_exprt string_constraint_generatort::of_string_concat(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string concat
  
  string_exprt s1 = string_of_expr(args[0]);
  string_exprt s2 = string_of_expr(args[1]);

  of_string_concat(s1, s2, axioms);
}



string_exprt string_constraint_generatort::of_string_copy(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1);
  
  string_exprt s1 = string_of_expr(args[0]);
  axioms.emplace_back(equal_exprt(length(), s1.length()));
  symbol_exprt idx = fresh_symbol("QA_index_copy",refined_string_typet::index_type());
  string_constraintt a1(equal_exprt(s1[idx],(*this)[idx]));
  axioms.push_back(a1.forall(idx, s1.length()));  
}

string_exprt string_constraint_generatort::of_string_set_length(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2);

  bool is_c_string = refined_string_typet::is_c_string_type(f.type());
  exprt null_char;
  if(is_c_string) null_char = constant_char(0);
  else null_char = constant_java_char(0);
  
  string_exprt s1 = string_of_expr(args[0]);

  // |s| = k 
  // && forall i < |s|. (i < k ==> s[i] = s1[i]) && (i >= k ==> s[i] = 0)

  axioms.emplace_back(equal_exprt(length(), args[1]));
  symbol_exprt idx = fresh_symbol("QA_index_set_length",refined_string_typet::index_type());

  
  string_constraintt a1
    (and_exprt(implies_exprt(s1 > idx, equal_exprt(s1[idx],(*this)[idx])),
	       implies_exprt(s1 <= idx, equal_exprt(s1[idx],null_char))));
  axioms.push_back(a1.forall(idx, length()));  
}



string_exprt string_constraint_generatort::of_java_char_array(const exprt & char_array, axiom_vect & axioms)
{
  exprt arr = to_address_of_expr(char_array).object();
  exprt len = member_exprt(arr, "length",length().type());
  exprt cont = member_exprt(arr, "data",content().type());
  op0() = len;
  op1() = cont;
}
 

string_exprt string_constraint_generatort::of_string_value_of(const function_application_exprt &f, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = f.arguments();
  if(args.size() == 3)
    {
      exprt char_array = args[0];
      exprt offset = args[1];
      exprt count = args[2];
      string_exprt str(refined_string_typet::java_char_type());
      str.of_java_char_array(args[0],axioms);
      axioms.emplace_back(equal_exprt(length(), count));
      
      symbol_exprt idx = fresh_symbol("QA_index_value_of",refined_string_typet::index_type());
      string_constraintt a1(equal_exprt(str[plus_exprt(idx,offset)],(*this)[idx]));
      axioms.push_back(a1.forall(idx, count));  
    }
  else
    {
      assert(args.size() == 1);
      of_java_char_array(args[0],axioms);
    }
}

string_exprt string_constraint_generatort::of_string_substring
(const function_application_exprt &expr)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() >= 2);

  string_exprt str = string_of_expr(args[0]);

  exprt i(args[1]);

  exprt j;
  if(args.size() == 3) j = args[2];
  else j = str.length();

  of_string_substring(str,i,j,symbol_to_string,axioms);
}

string_exprt string_constraint_generatort::of_string_substring
  (const string_exprt & str, const exprt & start, const exprt & end)
{
  symbol_exprt idx = fresh_symbol("index_substring", refined_string_typet::index_type());
  assert(start.type() == refined_string_typet::index_type());
  assert(end.type() == refined_string_typet::index_type());

  axioms.emplace_back(equal_exprt(length(), minus_exprt(end, start)));
  axioms.emplace_back(binary_relation_exprt(start, ID_lt, end));
  axioms.emplace_back(str >= end);

  // forall idx < str.length, str[idx] = arg_str[idx+i]
  string_constraintt a(equal_exprt((*this)[idx], str[plus_exprt(start, idx)]));
  
  axioms.push_back(a.forall(idx,length()));
}

string_exprt string_constraint_generatort::of_string_trim
(const function_application_exprt &expr)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 1);
  string_exprt str = string_of_expr(args[0]);
  symbol_exprt idx = fresh_symbol("index_trim", refined_string_typet::index_type());

  bool is_c_string = refined_string_typet::is_c_string_type(expr.type());
  exprt space_char = is_c_string ? constant_char(32) : constant_java_char(32);

  // m + |s1| <= |str|
  axioms.emplace_back(str >= plus_exprt(idx, length()));
  axioms.emplace_back(binary_relation_exprt(idx, ID_ge, refined_string_typet::index_zero()));
  axioms.emplace_back(str >= idx);
  axioms.emplace_back(str >= length());
  ///axioms.emplace_back(binary_relation_exprt(length(), ID_gt, index_zero));

  symbol_exprt n = fresh_symbol("QA_index_trim",refined_string_typet::index_type());
  // forall n < m, str[n] = ' '
  string_constraintt a(equal_exprt(str[n], space_char));
  axioms.push_back(a.forall(n,idx));

  symbol_exprt n2 = fresh_symbol("QA_index_trim2",refined_string_typet::index_type());
  // forall n < |str|-m-|s1|, str[m+|s1|+n] = ' '
  string_constraintt a1(equal_exprt(str[plus_exprt(idx,plus_exprt(length(),n2))], space_char));
  axioms.push_back(a1.forall(n2,minus_exprt(str.length(),plus_exprt(idx,length()))));

  symbol_exprt n3 = fresh_symbol("QA_index_trim3",refined_string_typet::index_type());
  // forall n < |s1|, s[idx+n] = s1[n]
  string_constraintt a2(equal_exprt((*this)[n3], str[plus_exprt(n3, idx)]));
  axioms.push_back(a2.forall(n3,length()));
  // (s[m] != ' ' && s[m+|s1|-1] != ' ') || m = |s|
  or_exprt m_index_condition(equal_exprt(idx,str.length()),
			     and_exprt
			     (not_exprt(equal_exprt(str[idx],space_char)),
			      not_exprt(equal_exprt(str[minus_exprt(plus_exprt(idx,length()),refined_string_typet::index_of_int(1))],space_char))));
  axioms.push_back(m_index_condition);
}

string_exprt string_constraint_generatort::of_string_to_lower_case
(const function_application_exprt &expr)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 1);

  string_exprt str = string_of_expr(args[0]);
  bool is_c_string = refined_string_typet::is_c_string_type(expr.type());
  exprt char_a;
  exprt char_A;
  exprt char_z;
  exprt char_Z;
  if(is_c_string) {
    char_a = constant_char(97);
    char_A = constant_char(65);
    char_z = constant_char(122);
    char_Z = constant_char(90);
  } else { 
    char_a = constant_char(97);
    char_A = constant_char(65);
    char_z = constant_char(122);
    char_Z = constant_char(90);
  }

  axioms.emplace_back(equal_exprt(length(), str.length()));

  symbol_exprt idx = fresh_symbol("QA_lower_case",refined_string_typet::index_type());
  // forall idx < str.length, this[idx] = 'A'<=str[idx]<='Z' ? str[idx]+'a'-'A' : str[idx]
  exprt is_upper_case = and_exprt(binary_relation_exprt(char_A,ID_le,str[idx]),
				  binary_relation_exprt(str[idx],ID_le,char_Z));
  equal_exprt convert((*this)[idx],plus_exprt(str[idx],minus_exprt(char_a,char_A)));
  equal_exprt eq((*this)[idx], str[idx]);
  string_constraintt a(and_exprt(implies_exprt(is_upper_case,convert),implies_exprt(not_exprt(is_upper_case),eq)));
  axioms.push_back(a.forall(idx,length()));
}


string_exprt string_constraint_generatort::of_string_to_upper_case
(const function_application_exprt &expr)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 1);

  string_exprt str = string_of_expr(args[0]);
  bool is_c_string = refined_string_typet::is_c_string_type(expr.type());
  exprt char_a;
  exprt char_A;
  exprt char_z;
  exprt char_Z;

  if(is_c_string) {
    char_a = constant_char(97);
    char_A = constant_char(65);
    char_z = constant_char(122);
    char_Z = constant_char(90);
  } else { 
    char_a = constant_char(97);
    char_A = constant_char(65);
    char_z = constant_char(122);
    char_Z = constant_char(90);
  }

  axioms.emplace_back(equal_exprt(length(), str.length()));

  symbol_exprt idx = fresh_symbol("QA_upper_case",refined_string_typet::index_type());
  // forall idx < str.length, this[idx] = 'a'<=str[idx]<='z' ? str[idx]+'A'-'a' : str[idx]
  exprt is_lower_case = and_exprt(binary_relation_exprt(char_a,ID_le,str[idx]),
				  binary_relation_exprt(str[idx],ID_le,char_z));
  equal_exprt convert((*this)[idx],plus_exprt(str[idx],minus_exprt(char_A,char_a)));
  equal_exprt eq((*this)[idx], str[idx]);
  string_constraintt a(and_exprt(implies_exprt(is_lower_case,convert),implies_exprt(not_exprt(is_lower_case),eq)));
  axioms.push_back(a.forall(idx,length()));
}


string_exprt string_constraint_generatort::of_int
(const function_application_exprt &expr,axiom_vect & axioms)
{
  assert(expr.arguments().size() == 1);
  of_int(expr.arguments()[0],axioms,refined_string_typet::is_c_string_type(expr.type()),10);
}

string_exprt string_constraint_generatort::of_long
(const function_application_exprt &expr,axiom_vect & axioms)
{
  assert(expr.arguments().size() == 1);
  of_int(expr.arguments()[0],axioms,refined_string_typet::is_c_string_type(expr.type()),30);
}


string_exprt string_constraint_generatort::of_float
(const function_application_exprt &f,axiom_vect & axioms)
{
  assert(f.arguments().size() == 1);
  of_float(f.arguments()[0],axioms,refined_string_typet::is_c_string_type(f.type()),false);
}

string_exprt string_constraint_generatort::of_float
(const exprt &f, axiom_vect & axioms, bool is_c_string, bool double_precision)
{
  // Warning: we currently only have partial specification
  unsignedbv_typet char_type;
  int char_width;
  if(is_c_string) {
    char_type = refined_string_typet::char_type();
    char_width = STRING_SOLVER_CHAR_WIDTH;
  } else {
    char_type = refined_string_typet::java_char_type();
    char_width = JAVA_STRING_SOLVER_CHAR_WIDTH;
  }

  axioms.emplace_back(binary_relation_exprt(length(), ID_le, refined_string_typet::index_of_int(24)));


  string_exprt magnitude(char_type);
  string_exprt sign_string(char_type);

  //     If the argument is NaN, the result is the string "NaN".
  string_exprt nan_string(char_type);
  nan_string.of_string_constant("NaN",char_width,char_type,axioms);

  ieee_float_spect fspec = double_precision?ieee_float_spect::double_precision():ieee_float_spect::single_precision();
  
  exprt isnan = float_bvt().isnan(f,fspec);
  axioms.emplace_back(isnan, equal_exprt(magnitude.length(),nan_string.length()));
  symbol_exprt qvar = string_exprt::fresh_symbol("qvar_equal_nan", refined_string_typet::index_type());
  axioms.push_back
    (string_constraintt(isnan,equal_exprt(magnitude[qvar],nan_string[qvar])
			).forall(qvar,nan_string.length()));

  // If the argument is not NaN, the result is a string that represents the sign and magnitude (absolute value) of the argument. If the sign is negative, the first character of the result is '-' ('\u002D'); if the sign is positive, no sign character appears in the result. 

  const bitvector_typet &bv_type=to_bitvector_type(f.type());
  unsigned width=bv_type.get_width();
  exprt isneg = extractbit_exprt(f, width-1);

  axioms.emplace_back(isneg, equal_exprt(sign_string.length(),refined_string_typet::index_of_int(1)));
  
  axioms.emplace_back(not_exprt(isneg), equal_exprt(sign_string.length(),refined_string_typet::index_of_int(0)));
  axioms.emplace_back(isneg,equal_exprt(sign_string[refined_string_typet::index_of_int(0)], constant_char(0x2D);


  // If m is infinity, it is represented by the characters "Infinity"; thus, positive infinity produces the result "Infinity" and negative infinity produces the result "-Infinity".

  string_exprt infinity_string(char_type);
  infinity_string.of_string_constant("Infinity",char_width,char_type,axioms);
  exprt isinf = float_bvt().isinf(f,fspec);
  axioms.emplace_back(isinf, equal_exprt(magnitude.length(),infinity_string.length()));
  symbol_exprt qvar_inf = string_exprt::fresh_symbol("qvar_equal_infinity", refined_string_typet::index_type());
  axioms.push_back
    (string_constraintt(isinf,equal_exprt(magnitude[qvar_inf],infinity_string[qvar_inf])
			).forall(qvar_inf,infinity_string.length()));

  //If m is zero, it is represented by the characters "0.0"; thus, negative zero produces the result "-0.0" and positive zero produces the result "0.0".

  string_exprt zero_string(char_type);
  zero_string.of_string_constant("0.0",char_width,char_type,axioms);
  exprt iszero = float_bvt().is_zero(f,fspec);
  axioms.emplace_back(iszero, equal_exprt(magnitude.length(),zero_string.length()));
  symbol_exprt qvar_zero = string_exprt::fresh_symbol("qvar_equal_zero", refined_string_typet::index_type());
  axioms.push_back
    (string_constraintt(iszero,equal_exprt(magnitude[qvar_zero],zero_string[qvar_zero])
			).forall(qvar_zero,zero_string.length()));

  
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

  of_string_concat(sign_string,magnitude,axioms);


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

string_exprt string_constraint_generatort::of_double
(const function_application_exprt &f,axiom_vect & axioms)
{
  assert(f.arguments().size() == 1);
  of_float(f.arguments()[0],axioms,refined_string_typet::is_c_string_type(f.type()),true);
}


string_exprt string_constraint_generatort::of_bool
(const function_application_exprt &f,axiom_vect & axioms)
{
  assert(f.arguments().size() == 1);
  of_bool(f.arguments()[0],axioms,refined_string_typet::is_c_string_type(f.type()));

}

string_exprt string_constraint_generatort::of_bool
(const exprt &i,axiom_vect & axioms,bool is_c_string)
{
  unsignedbv_typet char_type;
  int char_width;
  if(is_c_string) {
    char_type = refined_string_typet::char_type();
    char_width = STRING_SOLVER_CHAR_WIDTH;
  } else {
    char_type = refined_string_typet::java_char_type();
    char_width = JAVA_STRING_SOLVER_CHAR_WIDTH;
  }

  assert(i.type() == bool_typet() || i.type().id() == ID_c_bool);
  
  typecast_exprt eq(i,bool_typet());

  string_exprt true_string(char_type);
  string_exprt false_string(char_type);
  true_string.of_string_constant("true",char_width,char_type,axioms);
  false_string.of_string_constant("false",char_width,char_type,axioms);

  axioms.emplace_back(eq, equal_exprt(length(),true_string.length()));
  symbol_exprt qvar = string_exprt::fresh_symbol("qvar_equal_true", refined_string_typet::index_type());
  axioms.push_back
    (string_constraintt(eq,equal_exprt((*this)[qvar],true_string[qvar])
			).forall(qvar,true_string.length()));

  axioms.emplace_back(not_exprt(eq), equal_exprt(length(),false_string.length()));
  symbol_exprt qvar1 = string_exprt::fresh_symbol("qvar_equal_false", refined_string_typet::index_type());
  axioms.push_back
    (string_constraintt(not_exprt(eq),equal_exprt((*this)[qvar1],false_string[qvar1])
			).forall(qvar,false_string.length()));



}


string_exprt string_constraint_generatort::of_int
(const exprt &i,axiom_vect & axioms,bool is_c_string, int max_size)
{
  typet type = i.type();
  int width = type.get_unsigned_int(ID_width);
  exprt ten = constant_of_nat(10,width,type);
  exprt zero_char;
  exprt nine_char;
  exprt minus_char;

  if(is_c_string) {
    minus_char = constant_char(45);
    zero_char = constant_char(48);
    nine_char = constant_char(57);
    } else {     
    minus_char = constant_char(45);
    zero_char = constant_char(48);
    nine_char = constant_char(57);
  }

  axioms.emplace_back(and_exprt(*this > refined_string_typet::index_zero(),*this <= refined_string_typet::index_of_int(max_size)));

  exprt chr = (*this)[refined_string_typet::index_zero()];
  exprt starts_with_minus = equal_exprt(chr,minus_char);
  exprt starts_with_digit = and_exprt
    (binary_relation_exprt(chr,ID_ge,zero_char),
     binary_relation_exprt(chr,ID_le,nine_char));
  axioms.emplace_back(or_exprt(starts_with_digit,starts_with_minus));

  for(unsigned size=1; size<=max_size;size++) {
    exprt sum = constant_of_nat(0,width,type);
    exprt all_numbers = true_exprt();
    chr = (*this)[refined_string_typet::index_of_int(0)];
    exprt first_value = typecast_exprt(minus_exprt(chr,zero_char),type);

    for(unsigned j=1; j<size; j++) {
      chr = (*this)[refined_string_typet::index_of_int(j)];
      sum = plus_exprt(mult_exprt(sum,ten),typecast_exprt(minus_exprt(chr,zero_char),type));
      first_value = mult_exprt(first_value,ten);
      all_numbers = and_exprt(all_numbers,and_exprt
			      (binary_relation_exprt(chr,ID_ge,zero_char),
			       binary_relation_exprt(chr,ID_le,nine_char)));
    }

    equal_exprt premise(length(), refined_string_typet::index_of_int(size));
    axioms.emplace_back(and_exprt(premise,starts_with_digit),
    			and_exprt(equal_exprt(i,plus_exprt(sum,first_value)),
    				  all_numbers));

    axioms.emplace_back(and_exprt(premise,starts_with_minus),
			and_exprt(equal_exprt(i,unary_minus_exprt(sum)),
				  all_numbers));
    //disallow 0s at the beggining
    if(size>1) {
      axioms.emplace_back(and_exprt(premise,starts_with_digit),
			  not_exprt(equal_exprt((*this)[refined_string_typet::index_zero()],zero_char)));
      axioms.emplace_back(and_exprt(premise,starts_with_minus),
			  not_exprt(equal_exprt((*this)[refined_string_typet::index_of_int(1)],zero_char)));
			  }

    //we have to be careful when exceeding the maximal size of integers
    // Warning this should be different depending on max size
    if(size == max_size) {
      exprt smallest_with_10_digits = constant_of_nat(1000000000,width,type);
      axioms.emplace_back(premise,binary_relation_exprt(i,ID_ge,smallest_with_10_digits));
    }
  }
}


exprt int_of_hex_char(exprt chr, unsigned char_width, typet char_type) {
  exprt zero_char = constant_of_nat(48,char_width,char_type);
  exprt nine_char = constant_of_nat(57,char_width,char_type);
  exprt a_char = constant_of_nat(0x61,char_width,char_type);
  return if_exprt(binary_relation_exprt(chr,ID_gt,nine_char),
		  minus_exprt(chr,constant_of_nat(0x61 - 10,char_width,char_type)),
		  minus_exprt(chr,zero_char));
}


string_exprt string_constraint_generatort::of_int_hex
(const exprt &i,axiom_vect & axioms,bool is_c_string)
{
  typet type = i.type();
  int width = type.get_unsigned_int(ID_width);
  exprt sixteen = constant_of_nat(16,width,type);
  typet char_type;
  unsigned char_width;

  if(is_c_string) {
    char_type = refined_string_typet::char_type();
    char_width = STRING_SOLVER_CHAR_WIDTH;
  } else {
    char_type = refined_string_typet::java_char_type();
    char_width = JAVA_STRING_SOLVER_CHAR_WIDTH;
  }

  exprt minus_char = constant_of_nat(45,char_width,char_type);
  exprt zero_char = constant_of_nat(48,char_width,char_type);
  exprt nine_char = constant_of_nat(57,char_width,char_type);
  exprt a_char = constant_of_nat(0x61,char_width,char_type);
  exprt f_char = constant_of_nat(0x66,char_width,char_type);

  int max_size = 8;
  axioms.emplace_back(and_exprt(*this > refined_string_typet::index_zero(),*this <= refined_string_typet::index_of_int(max_size)));

  for(int size=1; size<=max_size;size++) {
    exprt sum = constant_of_nat(0,width,type);
    exprt all_numbers = true_exprt();
    exprt chr = (*this)[refined_string_typet::index_of_int(0)];

    for(int j=0; j<size; j++) {
      chr = (*this)[refined_string_typet::index_of_int(j)];
      sum = plus_exprt(mult_exprt(sum,sixteen),typecast_exprt(int_of_hex_char(chr,char_width,char_type),type));
      all_numbers = and_exprt
	(all_numbers,
	 or_exprt(and_exprt
		  (binary_relation_exprt(chr,ID_ge,zero_char),
		   binary_relation_exprt(chr,ID_le,nine_char)),
		  and_exprt
		  (binary_relation_exprt(chr,ID_ge,a_char),
		   binary_relation_exprt(chr,ID_le,f_char))));
    }

    equal_exprt premise(length(), refined_string_typet::index_of_int(size));
    axioms.emplace_back(premise,
    			and_exprt(equal_exprt(i,sum),all_numbers));
    
    //disallow 0s at the beggining
    if(size>1) {
      axioms.emplace_back(premise,
			  not_exprt(equal_exprt((*this)[refined_string_typet::index_zero()],zero_char)));
    }

  }
}

string_exprt string_constraint_generatort::of_int_hex
(const function_application_exprt &f,axiom_vect & axioms)
{
  assert(f.arguments().size() == 1);
  of_int_hex(f.arguments()[0],axioms,refined_string_typet::is_c_string_type(f.type()));
}

string_exprt string_constraint_generatort::of_char
(const function_application_exprt &f,axiom_vect & axioms)
{
  assert(f.arguments().size() == 1);
  of_char(f.arguments()[0],axioms,refined_string_typet::is_c_string_type(f.type()));

}

string_exprt string_constraint_generatort::of_char
(const exprt &c, axiom_vect & axioms, bool is_c_string)
{
  and_exprt lemma(equal_exprt((*this)[refined_string_typet::index_of_int(0)], c),
		  equal_exprt(length(), refined_string_typet::index_of_int(1)));
  axioms.push_back(lemma);

}


string_exprt string_constraint_generatort::of_code_point(const exprt &code_point, axiom_vect & axioms, bool is_c_string)
{
  typet type = code_point.type();
  binary_relation_exprt small(code_point,ID_lt,constant_of_nat(0x010000,32, type));
  axioms.emplace_back(small,
		      equal_exprt(length(), refined_string_typet::index_of_int(1)));
  axioms.emplace_back(not_exprt(small),
		      equal_exprt(length(), refined_string_typet::index_of_int(2)));
  axioms.emplace_back(small,equal_exprt((*this)[refined_string_typet::index_of_int(0)],typecast_exprt(code_point,refined_string_typet::java_char_type())));

  axioms.emplace_back(not_exprt(small),
		      equal_exprt
		      ((*this)[refined_string_typet::index_of_int(0)],
		       typecast_exprt
		       (plus_exprt(constant_of_nat(0xD800,32, type),
				   div_exprt(minus_exprt(code_point,constant_of_nat(0x010000,32,type)),constant_of_nat(0x0400,32, type))),
			refined_string_typet::java_char_type())));
  axioms.emplace_back(not_exprt(small),
		      equal_exprt
		      ((*this)[refined_string_typet::index_of_int(1)],
		       typecast_exprt
		       (plus_exprt(constant_of_nat(0xDC00,32, type),
				   mod_exprt(code_point,constant_of_nat(0x0400,32, type))),
			refined_string_typet::java_char_type())));

}


string_exprt string_constraint_generatort::of_string_char_set
(const function_application_exprt &expr)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); //bad args to string_char_set?

  string_exprt str = string_of_expr(args[0]);
  symbol_exprt c = fresh_symbol("char", refined_string_typet::get_char_type(args[0]));
  
  axioms.emplace_back(equal_exprt(c,args[2]));
  with_exprt sarrnew(str.content(), args[1], c);
  implies_exprt lemma(binary_relation_exprt(args[1], ID_lt, str.length()),
                      and_exprt(equal_exprt(content(), sarrnew),
                                equal_exprt(length(), str.length())));
  axioms.push_back(lemma);

}

string_exprt string_constraint_generatort::of_string_replace
(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();  
  assert(args.size() == 3); 
  string_exprt str = string_of_expr(args[0]);
  exprt oldChar = args[1];
  exprt newChar = args[2];

  axioms.emplace_back(equal_exprt(length(), str.length()));
  symbol_exprt qvar = string_exprt::fresh_symbol("QA_replace", refined_string_typet::index_type());

  axioms.push_back
    (string_constraintt
     (and_exprt
      (implies_exprt(equal_exprt(str[qvar],oldChar),equal_exprt((*this)[qvar],newChar)),
       implies_exprt(not_exprt(equal_exprt(str[qvar],oldChar)),
		     equal_exprt((*this)[qvar],str[qvar]))
       )
      ).forall(qvar,length()));

}

string_exprt string_constraint_generatort::of_string_delete_char_at
(const function_application_exprt &expr)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 2); 
  string_exprt str = string_of_expr(args[0]);
  exprt index_one = refined_string_typet::index_of_int(1);
  of_string_delete(str,args[1],plus_exprt(args[1],index_one),symbol_to_string,axioms);
}

string_exprt string_constraint_generatort::of_string_delete
(const string_exprt &str, const exprt & start, const exprt & end)
{
  // We should have these formulas:
  // (index < |str| ==> |s| = |str| - 1) && (index >= |str| ==> |s| = |str|)
  // forall i < |s| (i < index  ==> s[i] = str[i]
  //              && i >= index ==> s[i] = str[i+1])
  // However this may make the index set computation loop because the same 
  // index appears switched by one.
  // It may be better to call two substrings functions

  assert(start.type() == refined_string_typet::index_type());
  assert(end.type() == refined_string_typet::index_type());
  string_exprt str1(refined_string_typet::get_char_type(str));
  string_exprt str2(refined_string_typet::get_char_type(str));
  str1.of_string_substring(str,refined_string_typet::index_zero(),start,symbol_to_string,axioms);
  str2.of_string_substring(str,end,str.length(),symbol_to_string,axioms);
  of_string_concat(str1,str2,axioms);
  
}

string_exprt string_constraint_generatort::of_string_delete
(const function_application_exprt &expr)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); 
  string_exprt str = string_of_expr(args[0]);
  of_string_delete(str,args[1],args[2],symbol_to_string,axioms);
}


string_exprt string_constraint_generatort::of_string_concat_int(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_of_expr(args[0]);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_int(args[1],axioms,refined_string_typet::is_c_string_type(args[0].type()),10);
  of_string_concat(s1,s2,axioms);
}

string_exprt string_constraint_generatort::of_string_concat_long(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_of_expr(args[0]);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  
  s2.of_int(args[1],axioms,refined_string_typet::is_c_string_type(args[0].type()),30);
  of_string_concat(s1,s2,axioms);
}

string_exprt string_constraint_generatort::of_string_concat_bool(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_of_expr(args[0]);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_bool(args[1],axioms,refined_string_typet::is_c_string_type(f.type()));
  of_string_concat(s1,s2,axioms);
}

string_exprt string_constraint_generatort::of_string_concat_char(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_of_expr(args[0]);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_char(args[1],axioms,refined_string_typet::is_c_string_type(f.type()));
  of_string_concat(s1,s2,axioms);
}

string_exprt string_constraint_generatort::of_string_concat_double(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_of_expr(args[0]);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_float(args[1],axioms,refined_string_typet::is_c_string_type(f.type()),30);
  of_string_concat(s1,s2,axioms);
}

string_exprt string_constraint_generatort::of_string_concat_float(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_of_expr(args[0]);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_float(args[1],axioms,refined_string_typet::is_c_string_type(f.type()),10);
  of_string_concat(s1,s2,axioms);
}

string_exprt string_constraint_generatort::of_string_concat_code_point(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_code_point(args[1],axioms,refined_string_typet::is_c_string_type(f.type()));
  of_string_concat(s1,s2,axioms);
}

string_exprt string_constraint_generatort::of_string_insert(const string_exprt & s1, const string_exprt & s2, 
		      const exprt & offset, 
		      std::map<irep_idt, string_exprt> & symbol_to_string, 
		      axiom_vect & axioms) 
{
  assert(offset.type() == refined_string_typet::index_type());
  unsignedbv_typet char_type = refined_string_typet::get_char_type(s1);
  string_exprt pref(char_type);
  string_exprt suf(char_type);
  string_exprt concat1(char_type);
  pref.of_string_substring(s1,refined_string_typet::index_zero(),offset,symbol_to_string,axioms);
  suf.of_string_substring(s1,offset,s1.length(),symbol_to_string,axioms);
  concat1.of_string_concat(pref,s2,axioms);
  of_string_concat(concat1,suf,axioms);
}


string_exprt string_constraint_generatort::of_string_insert(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2 = string_of_expr(args[2],symbol_to_string,axioms); 
  of_string_insert(s1, s2, args[1],symbol_to_string, axioms);
}

string_exprt string_constraint_generatort::of_string_insert_int(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[2]));
  s2.of_int(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()),10);
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}

string_exprt string_constraint_generatort::of_string_insert_long(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[2]));
  s2.of_int(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()),30);
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}

string_exprt string_constraint_generatort::of_string_insert_bool(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_bool(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()));
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}

string_exprt string_constraint_generatort::of_string_insert_char(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_char(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()));
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}

string_exprt string_constraint_generatort::of_string_insert_double(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_float(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()),30);
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}

string_exprt string_constraint_generatort::of_string_insert_float(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_float(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()),10);
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}


#include <iostream>

string_exprt string_constraint_generatort::of_string_format(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  // warning this is right now only for java:
  bool is_c_string = false;
  unsignedbv_typet char_type = is_c_string?refined_string_typet::char_type():refined_string_typet::java_char_type();
  size_t char_width = is_c_string?STRING_SOLVER_CHAR_WIDTH:JAVA_STRING_SOLVER_CHAR_WIDTH;

  if(args.size() == 2) 
    {

      // Warning: this is not very clean:
      irep_idt literal = extract_java_string(to_symbol_expr(args[0].op1().op0().op0()));
      std::string format_string = id2string(literal);
      std::cout << "string_exprt::of_string_format " << format_string << std::endl;
      size_t position = format_string.find_first_of('%');
      std::vector<string_exprt> strings;
      int arg_counter = 0;

      string_exprt begin(char_type);
      begin.of_string_constant(format_string.substr(0,position),char_width,char_type,axioms);
      strings.push_back(begin);
      //std::cout << "string_exprt::of_string_format : " << f.pretty() << std::endl;
      //typecast_exprt arg_tab(member_exprt(args[1].op0(),"data"),array_typet(java_type_from_string("Ljava/lang/Object;"),infinity_exprt(refined_string_typet::index_type())));
      member_exprt arg_tab(args[1].op0(),"data",array_typet(java_type_from_string("Ljava/lang/Object;"),infinity_exprt(refined_string_typet::index_type())));
      std::cout << "string_exprt::arg_tab : " << arg_tab.type().pretty() << std::endl;

      while(position != std::string::npos) 
	{
	  switch(format_string[position+1]) {
	  case 'd' : 
	    {
	    string_exprt str(char_type);
	    index_exprt arg_object(arg_tab,refined_string_typet::index_of_int(arg_counter++)); 
	    typecast_exprt arg_int(arg_object, signedbv_typet(32));
	    symbol_exprt var_arg_int = string_exprt::fresh_symbol("format_arg_int", signedbv_typet(32));
	    axioms.push_back(equal_exprt(arg_int,var_arg_int));
	    axioms.push_back(equal_exprt(var_arg_int,refined_string_typet::index_of_int(12)));
	    str.of_int(var_arg_int,axioms,is_c_string,10);

	    strings.push_back(str);
	    std::cout << "string format: position " << position << " int arg: " << arg_int.pretty() << std::endl;
	    break;
	    }

	  default:
	    {
	      std::cout << "warning: unknown string format: " << format_string << std::endl;
	      break;
	    }
	  }
	  size_t new_position = format_string.find_first_of('%',position+2);
	  if(new_position != std::string::npos) {
	    string_exprt str(char_type);
	    str.of_string_constant(format_string.substr(position+2,new_position),char_width,char_type,axioms);
	    strings.push_back(str);
	  }
	  position = new_position;
	}

     
      string_exprt * concatenation = &strings[0];
      int i;
      for(i = 1; i < strings.size() - 1; i++)
	{
	  string_exprt str(refined_string_typet::java_char_type());
	  str.of_string_concat(*concatenation,strings[i],axioms);
	  concatenation = &str;
	}
      
      of_string_concat(*concatenation,strings[i],axioms);
    }
  
}

void string_constraint_generator::make_string(const symbol_exprt & sym, const exprt & str) 
{
  //debug() << "string_constraint_generatort::make_string of " << pretty_short(sym) << eom;
  //<< " --> " << pretty_short(str) << eom;
  if(str.id()==ID_symbol) 
    assign_to_symbol(sym,string_of_symbol(to_symbol_expr(str)));
  else {
    // assign_to_symbol(sym,string_exprt::of_expr(str,symbol_to_string,string_axioms));
    if (str.id() == ID_function_application && 
	starts_with(to_symbol_expr(to_function_application_expr(str).function()).get_identifier(),cprover_string_intern_func)) {
	  symbol_exprt sym1 = convert_string_intern(to_function_application_expr(str));
	  string_exprt s(refined_string_typet::java_char_type());
	  assign_to_symbol(sym1,s);
	  assign_to_symbol(sym,s);
	}
	else 
	  assign_to_symbol(sym,string_exprt::of_expr(str,symbol_to_string,string_axioms));
  }
  //debug() << "string = " << symbol_to_string[sym.get_identifier()].pretty() << eom;
}

string_exprt string_constraint_generator::make_string(const exprt & str) 
{
  //debug() << "string_constraint_generatort::make_string of " << pretty_short(str) << eom;
  if(str.id()==ID_symbol) 
    return string_of_symbol(to_symbol_expr(str));
  else
    if (str.id() == ID_function_application &&
	starts_with(to_symbol_expr(to_function_application_expr(str).function()).get_identifier(),cprover_string_intern_func)) { 
      symbol_exprt sym1 = convert_string_intern(to_function_application_expr(str));
      string_exprt s(refined_string_typet::java_char_type());
      assign_to_symbol(sym1,s);
      return s;
    }
    else
      return string_exprt::of_expr(str,symbol_to_string,string_axioms);
}



exprt string_constraint_generatort::convert_string_equal(const function_application_exprt &f) {
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);
  
  symbol_exprt eq = fresh_boolean("equal");
  typecast_exprt tc_eq(eq,f.type());

  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string equal?

  string_exprt s1 = make_string(args[0]);
  string_exprt s2 = make_string(args[1]);

  // We want to write:
  // eq <=> (s1.length = s2.length  && forall i < s1.length. s1[i] = s2[i])
  // We can't do it directly because of the universal quantification inside.
  // So we say instead the three following:
  // eq => s1.length = s2.length
  // forall i < s1.length. eq => s1[i] = s2[i]
  // !eq => s1.length != s2.length || (witness < s1.length && s1[witness] != s2[witness])

  symbol_exprt witness = fresh_index("witness_unequal");
  symbol_exprt qvar = string_exprt::fresh_symbol("qvar_equal", index_type);

  string_axioms.emplace_back(eq, equal_exprt(s1.length(), s2.length()));

  string_axioms.push_back
    (string_constraintt(eq,equal_exprt(s1[qvar],s2[qvar])
			).forall(qvar,zero,s1.length()));

  string_axioms.emplace_back
    (not_exprt(eq),
     or_exprt(notequal_exprt(s1.length(), s2.length()),
	      string_constraintt(notequal_exprt(s1[witness],s2[witness])).exists(witness,zero,s1.length())));

  return tc_eq;
}

exprt character_equals_ignore_case(exprt char1, exprt char2, exprt char_a, exprt char_A, exprt char_Z) {
  exprt is_upper_case_1 = and_exprt(binary_relation_exprt(char_A,ID_le,char1),
				  binary_relation_exprt(char1,ID_le,char_Z));
  exprt is_upper_case_2 = and_exprt(binary_relation_exprt(char_A,ID_le,char2),
				  binary_relation_exprt(char2,ID_le,char_Z));
  return or_exprt(or_exprt(equal_exprt(char1,char2),
			   and_exprt(is_upper_case_1, equal_exprt(minus_exprt(plus_exprt(char_a,char1),char_A),char2))),
		  and_exprt(is_upper_case_2, equal_exprt(minus_exprt(plus_exprt(char_a,char2),char_A),char1)));
}

exprt string_constraint_generatort::convert_string_equals_ignore_case(const function_application_exprt &f) {
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);
  
  symbol_exprt eq = fresh_boolean("equal_ignore_case");
  typecast_exprt tc_eq(eq,f.type());

  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string equal?

  bool is_c_string = refined_string_typet::is_c_string_type(f.type());
  exprt char_a;
  exprt char_A;
  exprt char_Z;
  if(is_c_string) {
    char_a = constant_of_nat(97,refined_string_typet::char_type());
    char_A = constant_of_nat(65,refined_string_typet::char_type());
    char_Z = constant_of_nat(90,refined_string_typet::char_type());
  } else { 
    char_a = constant_of_nat(97,refined_string_typet::java_char_type());
    char_A = constant_of_nat(65,refined_string_typet::java_char_type());
    char_Z = constant_of_nat(90,refined_string_typet::java_char_type());
  }

  string_exprt s1 = make_string(args[0]);
  string_exprt s2 = make_string(args[1]);
  symbol_exprt witness = fresh_index("witness_unequal_ignore_case");
  symbol_exprt qvar = string_exprt::fresh_symbol("qvar_equal_ignore_case", index_type);

  string_axioms.emplace_back(eq, equal_exprt(s1.length(), s2.length()));

  string_axioms.push_back
    (string_constraintt(eq,character_equals_ignore_case(s1[qvar],s2[qvar],char_a,char_A,char_Z)
			).forall(qvar,zero,s1.length()));

  string_axioms.emplace_back
    (not_exprt(eq),
     or_exprt(notequal_exprt(s1.length(), s2.length()),
	      string_constraintt(not_exprt(character_equals_ignore_case(s1[witness],s2[witness],char_a,char_A,char_Z))).exists(witness,zero,s1.length())));

  return tc_eq;
}


bvt string_constraint_generatort::convert_string_length(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); 
  string_exprt str = make_string(args[0]);
  exprt length = str.length();
  return tmp_c_o_n_v_e_r_t_bv(length);
}

exprt string_constraint_generatort::is_positive(const exprt & x)
{ return binary_relation_exprt(x, ID_ge, refined_string_typet::index_of_int(0)); }


exprt string_constraint_generatort::convert_string_is_prefix(const string_exprt &prefix, const string_exprt &str, const exprt & offset)
{
  symbol_exprt isprefix = fresh_boolean("isprefix");
  string_axioms.emplace_back(isprefix, str >= plus_exprt(prefix.length(),offset));

  // forall 0 <= witness < prefix.length. isprefix => s0[witness+offset] = s2[witness]
  symbol_exprt qvar = string_exprt::fresh_symbol("QA_isprefix", index_type);
  string_axioms.push_back
    (string_constraintt(isprefix, equal_exprt(str[plus_exprt(qvar,offset)],prefix[qvar])
			).forall(qvar,zero,prefix.length()));
	     
  symbol_exprt witness = fresh_index("witness_not_isprefix");

  or_exprt s0_notpref_s1(not_exprt(str >= plus_exprt(prefix.length(),offset)),
			 and_exprt
			 (str >= plus_exprt(prefix.length(),offset),
			  and_exprt(binary_relation_exprt(witness,ID_ge,zero),
				    and_exprt(prefix > witness, 
					      notequal_exprt(str[plus_exprt(witness,offset)],prefix[witness])))));
		       
  string_axioms.emplace_back(implies_exprt (not_exprt(isprefix),s0_notpref_s1));
  return isprefix; 
}

exprt string_constraint_generatort::convert_string_is_prefix
(const function_application_exprt &f, bool swap_arguments)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);
  string_exprt s0 = make_string(args[swap_arguments?1:0]);
  string_exprt s1 = make_string(args[swap_arguments?0:1]);
  exprt offset;

  if(args.size() == 2) offset = zero;
  else if (args.size() == 3) offset = args[2];

  return typecast_exprt(convert_string_is_prefix(s0,s1,offset),f.type());
}

exprt string_constraint_generatort::convert_string_is_empty
(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1);
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);

  symbol_exprt is_empty = fresh_boolean("is_empty");
  string_exprt s0 = make_string(args[0]);
  string_axioms.emplace_back(implies_exprt(is_empty, equal_exprt(s0.length(),zero)));
  string_axioms.emplace_back(implies_exprt(equal_exprt(s0.length(),zero),is_empty));
  return typecast_exprt(is_empty,f.type());

}

bvt string_constraint_generatort::convert_string_is_suffix
(const function_application_exprt &f, bool swap_arguments)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string issuffix?
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);

  symbol_exprt issuffix = fresh_boolean("issuffix");
  typecast_exprt tc_issuffix(issuffix,f.type());
  string_exprt s0 = make_string(args[swap_arguments?1:0]);
  string_exprt s1 = make_string(args[swap_arguments?0:1]);


  // issufix(s1,s0) => s0.length >= s1.length
  // && forall witness < s1.length. 
  //     issufix => s1[witness] = s0[witness + s0.length - s1.length]
  // && !issuffix => s1.length > s0.length 
  //       || (s1.length > witness && s1[witness] != s0[witness + s0.length - s1.length]

  string_axioms.emplace_back(implies_exprt(issuffix, s1 >= s0));

  symbol_exprt qvar = string_exprt::fresh_symbol("QA_suffix", index_type);
  exprt qvar_shifted = plus_exprt(qvar, 
				  minus_exprt(s1.length(), s0.length()));
  string_axioms.push_back
    (string_constraintt(issuffix, equal_exprt(s0[qvar],s1[qvar_shifted])
			).forall(qvar,zero,s0.length()));

  symbol_exprt witness = fresh_index("witness_not_suffix");

  exprt shifted = plus_exprt(witness, 
			     minus_exprt(s1.length(), s0.length()));

  implies_exprt lemma2(not_exprt(issuffix),
		       and_exprt(is_positive(witness),
				 or_exprt(s0 > s1,
					  and_exprt(s0 > witness, 
						    notequal_exprt(s0[witness],s1[shifted])))));

  string_axioms.emplace_back(lemma2);

  return tmp_c_o_n_v_e_r_t_bv(tc_issuffix);
}


bvt string_constraint_generatort::convert_string_contains(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string contains?
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);

  symbol_exprt contains = fresh_boolean("contains");
  typecast_exprt tc_contains(contains,f.type());
  string_exprt s0 = make_string(args[0]);
  string_exprt s1 = make_string(args[1]);

  // contains => s0.length >= s1.length
  // && startpos <= s0.length - s1.length
  // && forall qvar < s1.length.
  //     contains => s1[qvar] = s0[startpos + qvar]
  // !contains => s1.length > s0.length 
  //       || (forall startpos <= s0.length - s1.length. 
  //             exists witness < s1.length && s1[witness] != s0[witness + startpos]

  string_axioms.emplace_back(implies_exprt(contains, s0 >= s1));

  symbol_exprt startpos = fresh_index("startpos_contains");

  string_axioms.emplace_back(//implies_exprt(contains,
			     and_exprt(is_positive(startpos),binary_relation_exprt(startpos, ID_le, minus_exprt(s0.length(),s1.length()))));

  symbol_exprt qvar = string_exprt::fresh_symbol("QA_contains", index_type);
  exprt qvar_shifted = plus_exprt(qvar, startpos);
  string_axioms.push_back
    (string_constraintt(contains,equal_exprt(s1[qvar],s0[qvar_shifted])
			).forall(qvar,zero,s1.length()));

  // We rewrite the axiom for !contains as:
  // forall startpos <= |s0| - |s1|.  (!contains && |s0| >= |s1| )
  //      ==> exists witness < |s1|. s1[witness] != s0[startpos+witness]

  string_axioms.push_back
    (string_constraintt::not_contains
     (zero,plus_exprt(refined_string_typet::index_of_int(1),minus_exprt(s0.length(),s1.length())), 
      and_exprt(not_exprt(contains),s0 >= s1),zero,s1.length(),s0,s1));

  return tmp_c_o_n_v_e_r_t_bv(tc_contains);
}


symbol_exprt string_constraint_generatort::fresh_index(const irep_idt &prefix){
  symbol_exprt i = string_exprt::fresh_symbol(prefix,index_type);
  index_symbols.push_back(i);
  return i;
}

symbol_exprt string_constraint_generatort::fresh_boolean(const irep_idt &prefix){
  symbol_exprt b = string_exprt::fresh_symbol(prefix,bool_typet());
  boolean_symbols.push_back(b);
  return b;
}

exprt string_constraint_generatort::convert_string_hash_code(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  string_exprt str = make_string(args[0]);
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
    symbol_exprt i = string_exprt::fresh_symbol("index_hash", refined_string_typet::index_type());
    string_axioms.emplace_back
      (or_exprt
       (equal_exprt(hash[it->second],hash[str]),
	or_exprt
	(not_exprt(equal_exprt(it->second.length(),str.length())),
	 and_exprt(equal_exprt(it->second.length(),str.length()),
		   and_exprt
		   (not_exprt(equal_exprt(str[i],it->second[i])),
		    and_exprt(str>i,binary_relation_exprt(i,ID_ge,zero )))
		   ))));
  }
			

  return hash[str];
}

exprt string_constraint_generatort::convert_string_index_of(const string_exprt &str, const exprt & c, const exprt & from_index){
  symbol_exprt index = fresh_index("index_of");
  symbol_exprt contains = fresh_boolean("contains_in_index_of");

  // from_index <= i < |s| && (i = -1 <=> !contains) && (contains => i >= from_index && s[i] = c)
  // && forall n. from_index <= n < i => s[n] != c 
  
  string_axioms.push_back(string_constraintt(equal_exprt(index,refined_string_typet::index_of_int(-1)),not_exprt(contains)).exists(index,refined_string_typet::index_of_int(-1),str.length()));
  string_axioms.emplace_back(not_exprt(contains),equal_exprt(index,refined_string_typet::index_of_int(-1)));
  string_axioms.emplace_back(contains,and_exprt(binary_relation_exprt(from_index,ID_le,index),equal_exprt(str[index],c)));

  symbol_exprt n = string_exprt::fresh_symbol("QA_index_of",index_type);

  string_axioms.push_back(string_constraintt(contains,not_exprt(equal_exprt(str[n],c))).forall(n,from_index,index));

  symbol_exprt m = string_exprt::fresh_symbol("QA_index_of",index_type);

  string_axioms.push_back(string_constraintt(not_exprt(contains),not_exprt(equal_exprt(str[m],c))).forall(m,from_index,str.length()));

  return index;
}

exprt string_constraint_generatort::convert_string_index_of_string(const string_exprt &str, const string_exprt & substring, const exprt & from_index)
{
  symbol_exprt offset = fresh_index("index_of");
  
  symbol_exprt contains = fresh_boolean("contains_substring");
  string_axioms.emplace_back(contains, and_exprt
			     (str >= plus_exprt(substring.length(),offset),
			      binary_relation_exprt(offset,ID_ge,from_index)));
  string_axioms.emplace_back(not_exprt(contains), equal_exprt(offset,refined_string_typet::index_of_int(-1)));
  
  // forall 0 <= witness < substring.length. contains => str[witness+offset] = substring[witness]
  symbol_exprt qvar = string_exprt::fresh_symbol("QA_index_of_string", index_type);
  string_axioms.push_back
    (string_constraintt(contains, equal_exprt(str[plus_exprt(qvar,offset)],substring[qvar])
			).forall(qvar,zero,substring.length()));
	     

  debug() << "string_constraint_generatort::convert_string_index_of_string : warning the stpecification is only partial" << eom;

  return offset; 
}

exprt string_constraint_generatort::convert_string_last_index_of_string(const string_exprt &str, const string_exprt & substring, const exprt & from_index)
{
  symbol_exprt offset = fresh_index("index_of");
  
  symbol_exprt contains = fresh_boolean("contains_substring");
  string_axioms.emplace_back(contains, and_exprt
			     (str >= plus_exprt(substring.length(),offset),
			      binary_relation_exprt(offset,ID_le,from_index)));
  string_axioms.emplace_back(not_exprt(contains), equal_exprt(offset,refined_string_typet::index_of_int(-1)));
  
  // forall 0 <= witness < substring.length. contains => str[witness+offset] = substring[witness]
  symbol_exprt qvar = string_exprt::fresh_symbol("QA_index_of_string", index_type);
  string_axioms.push_back
    (string_constraintt(contains, equal_exprt(str[plus_exprt(qvar,offset)],substring[qvar])
			).forall(qvar,zero,substring.length()));

  debug() << "string_constraint_generatort::convert_string_last_index_of_string : warning the stpecification is only partial" << eom;
  return offset; 
}


exprt string_constraint_generatort::convert_string_index_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(f.type() == index_type);
  string_exprt str = make_string(args[0]);
  exprt c = args[1];
  exprt from_index;

  if(args.size() == 2) from_index = zero;
  else if (args.size() == 3) from_index = args[2];
  else assert(false);

  if(refined_string_typet::is_java_string_type(c.type())){
    string_exprt sub = make_string(c);
    return convert_string_index_of_string(str,sub,from_index);    
  } else {
    if(!(c.type() == char_type || c.type() == java_char_type)){
      debug() << "warning: argument to string_index_of does not have char type: " 
	      << c.type().pretty() << eom;    
      c = typecast_exprt(c,java_char_type);
    }
    return convert_string_index_of(str,c,from_index);    
  }

}

exprt string_constraint_generatort::convert_string_last_index_of(const string_exprt &str, const exprt & c, const exprt & from_index) {
  symbol_exprt index = fresh_index("last_index_of");
  symbol_exprt contains = fresh_boolean("contains_in_last_index_of");

  // -1 <= i <= from_index && (i = -1 <=> !contains) && (contains => i <= from_index && s[i] = c)
  // && forall n. i <= n <= from_index => s[n] != c 

  exprt from_index_plus_one = plus_exprt(from_index,refined_string_typet::index_of_int(1));
  string_axioms.push_back(string_constraintt(equal_exprt(index,refined_string_typet::index_of_int(-1)),not_exprt(contains)).exists(index,refined_string_typet::index_of_int(-1),from_index_plus_one));
  string_axioms.emplace_back(not_exprt(contains),equal_exprt(index,refined_string_typet::index_of_int(-1)));
  string_axioms.emplace_back(contains,and_exprt(binary_relation_exprt(zero,ID_le,index),and_exprt(binary_relation_exprt(from_index,ID_ge,index),equal_exprt(str[index],c))));
  
  symbol_exprt n = string_exprt::fresh_symbol("QA_last_index_of",index_type);
  string_axioms.push_back(string_constraintt(contains,not_exprt(equal_exprt(str[n],c))).forall(n,plus_exprt(index,refined_string_typet::index_of_int(1)),from_index_plus_one));

  symbol_exprt m = string_exprt::fresh_symbol("QA_last_index_of",index_type);
  string_axioms.push_back(string_constraintt(not_exprt(contains),not_exprt(equal_exprt(str[m],c))).forall(m,zero,from_index_plus_one));

  return index;

}

exprt string_constraint_generatort::convert_string_last_index_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(f.type() == index_type);
  string_exprt str = make_string(args[0]);
  exprt c = args[1];
  exprt from_index;

  if(args.size() == 2) from_index = minus_exprt(str.length(),refined_string_typet::index_of_int(1));
  else if (args.size() == 3) from_index = args[2];
  else assert(false);

  if(refined_string_typet::is_java_string_type(c.type())){
    string_exprt sub = make_string(c);
    return convert_string_last_index_of_string(str,sub,from_index);    
  } else {
    if(!(c.type() == char_type || c.type() == java_char_type)){
      debug() << "warning: argument to string_index_of does not have char type: " 
	      << c.type().pretty() << eom;    
      c = typecast_exprt(c,java_char_type);
    }
    return convert_string_last_index_of(str,c,from_index);
  }
}

bvt string_constraint_generatort::convert_char_literal(
  const function_application_exprt &f)
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
    
    return tmp_c_o_n_v_e_r_t_bv(constant_exprt(binary, char_type));
  }
  else {
    throw "convert_char_literal unimplemented";
  }
    
}


bvt string_constraint_generatort::convert_string_char_at(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //string_char_at expects 2 arguments
  string_exprt str = make_string(args[0]);

  if(f.type() == char_type) {
    symbol_exprt char_sym = string_exprt::fresh_symbol("char",char_type);
    string_axioms.emplace_back(equal_exprt(char_sym,str[args[1]]));
    return tmp_c_o_n_v_e_r_t_bv(char_sym);
  } else {
    assert(f.type() == java_char_type);
    symbol_exprt char_sym = string_exprt::fresh_symbol("char",java_char_type);
    string_axioms.emplace_back(equal_exprt(char_sym,str[args[1]]));
    return tmp_c_o_n_v_e_r_t_bv(char_sym);
  }
}



constant_exprt string_constraint_generatort::constant_of_nat(int i,typet t) {
  return constant_exprt(integer2binary(i, boolbv_width(t)), t);
}

exprt string_constraint_generatort::convert_string_parse_int
(const function_application_exprt &expr)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 1);

  string_exprt str = make_string(args[0]);
  typet type = expr.type();
  symbol_exprt i = string_exprt::fresh_symbol("parsed_int",type);

  exprt zero_char;
  exprt minus_char;  
  exprt plus_char;
  if(refined_string_typet::is_c_string_type(args[0].type())) {
    plus_char = constant_of_nat(43,refined_string_typet::char_type());
    minus_char = constant_of_nat(45,refined_string_typet::char_type());
    zero_char = constant_of_nat(48,refined_string_typet::char_type());
  }
  else {
    plus_char = constant_of_nat(43,refined_string_typet::java_char_type());
    minus_char = constant_of_nat(45,refined_string_typet::java_char_type());
    zero_char = constant_of_nat(48,refined_string_typet::java_char_type());
  }

  exprt ten = constant_of_nat(10,type);

  exprt chr = str[refined_string_typet::index_of_int(0)];
  exprt starts_with_minus = equal_exprt(chr,minus_char);
  exprt starts_with_plus = equal_exprt(chr,plus_char);
  exprt starts_with_digit = binary_relation_exprt(chr,ID_ge,zero_char); 
  
  for(int size=1; size<=10;size++) {
    exprt sum = constant_of_nat(0,type);
    exprt first_value = typecast_exprt(minus_exprt(chr,zero_char),type);
    
    for(int j=1; j<size; j++){
      sum = plus_exprt(mult_exprt(sum,ten),typecast_exprt(minus_exprt(str[refined_string_typet::index_of_int(j)],zero_char),type));
      first_value = mult_exprt(first_value,ten);
    }

    equal_exprt premise(str.length(), refined_string_typet::index_of_int(size));
    string_axioms.emplace_back(and_exprt(premise,starts_with_digit),equal_exprt(i,plus_exprt(sum,first_value)));
    string_axioms.emplace_back(and_exprt(premise,starts_with_plus),equal_exprt(i,sum));
    string_axioms.emplace_back(and_exprt(premise,starts_with_minus),equal_exprt(i,unary_minus_exprt(sum)));
  }
  return i;
}


exprt string_constraint_generatort::is_high_surrogate(const exprt & chr) {
  return and_exprt
    (binary_relation_exprt(chr,ID_ge,constant_of_nat(0xD800,refined_string_typet::java_char_type())),
     binary_relation_exprt(chr,ID_le,constant_of_nat(0xDBFF,refined_string_typet::java_char_type())));
}
exprt string_constraint_generatort::is_low_surrogate(const exprt & chr) {
  return and_exprt
    (binary_relation_exprt(chr,ID_ge,constant_of_nat(0xDC00,refined_string_typet::java_char_type())),
     binary_relation_exprt(chr,ID_le,constant_of_nat(0xDFFF,refined_string_typet::java_char_type())));
}

exprt string_constraint_generatort::convert_string_code_point_at(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2);
  typet return_type = f.type();
  string_exprt str = make_string(args[0]);
  symbol_exprt result = string_exprt::fresh_symbol("char",return_type);

  exprt char1_as_int = typecast_exprt(str[args[1]],return_type);
  exprt char2_as_int = typecast_exprt(str[plus_exprt(args[1],refined_string_typet::index_of_int(1))],return_type);

  exprt pair_value = 
    plus_exprt
    (constant_of_nat(0x010000,return_type),
     (plus_exprt
      (mult_exprt
       (mod_exprt(char1_as_int,constant_of_nat(0x0800,return_type)),
	constant_of_nat(0x0400,return_type)),
       mod_exprt(char2_as_int,constant_of_nat(0x0400,return_type)))));
  
  exprt return_pair = and_exprt(is_high_surrogate(str[args[1]]),
				is_low_surrogate(str[plus_exprt(args[1],refined_string_typet::index_of_int(1))]));

  string_axioms.emplace_back(return_pair,equal_exprt(result,pair_value));
  string_axioms.emplace_back(not_exprt(return_pair),
			     equal_exprt(result,char1_as_int));
  return result;
}

exprt string_constraint_generatort::convert_string_code_point_before(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2);
  typet return_type = f.type();
  symbol_exprt result = string_exprt::fresh_symbol("char",return_type);
  string_exprt str = make_string(args[0]);

  exprt char1 = str[minus_exprt(args[1],refined_string_typet::index_of_int(2))];
  exprt char1_as_int = typecast_exprt(char1,return_type);
  exprt char2 = str[minus_exprt(args[1],refined_string_typet::index_of_int(1))];
  exprt char2_as_int = typecast_exprt(char2,return_type);

  exprt pair_value = 
    plus_exprt
    (constant_of_nat(0x010000,return_type),
     (plus_exprt
      (mult_exprt
       (mod_exprt(char1_as_int,constant_of_nat(0x0800,return_type)),
	constant_of_nat(0x0400,return_type)),
       mod_exprt(char2_as_int,constant_of_nat(0x0400,return_type)))));
  
  exprt return_pair = and_exprt(is_high_surrogate(char1),is_low_surrogate(char2));

  string_axioms.emplace_back(return_pair,equal_exprt(result,pair_value));
  string_axioms.emplace_back(not_exprt(return_pair),
			     equal_exprt(result,char2_as_int));
  return result;
}

exprt string_constraint_generatort::convert_string_code_point_count(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3);
  string_exprt str = make_string(args[0]);
  exprt begin = args[1];
  exprt end = args[2];
  typet return_type = f.type();
  symbol_exprt result = string_exprt::fresh_symbol("code_point_count",return_type);
  exprt length = minus_exprt(end,begin);
  string_axioms.emplace_back(binary_relation_exprt(result,ID_le,length));
  string_axioms.emplace_back(binary_relation_exprt(result,ID_ge,div_exprt(length,refined_string_typet::index_of_int(2))));

  return result;
}

exprt string_constraint_generatort::convert_string_offset_by_code_point(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3);
  string_exprt str = make_string(args[0]);
  exprt index = args[1];
  exprt offset = args[2];
  typet return_type = f.type();
  symbol_exprt result = string_exprt::fresh_symbol("offset_by_code_point",return_type);
  exprt minimum = plus_exprt(index,plus_exprt(index,offset));
  exprt maximum = plus_exprt(index,plus_exprt(index,mult_exprt(offset,refined_string_typet::index_of_int(2))));
  string_axioms.emplace_back(binary_relation_exprt(result,ID_le,maximum));
  string_axioms.emplace_back(binary_relation_exprt(result,ID_ge,minimum));

  return result;
}

// We compute the index set for all formulas, instantiate the formulas
// with the found indexes, and add them as lemmas.
void string_constraint_generatort::add_instantiations()
{
  debug() << "string_constraint_generatort::add_instantiations: "
	  << "going through the current index set:" << eom;
  for (std::map<exprt, expr_sett>::iterator i = current_index_set.begin(),
	 end = current_index_set.end(); i != end; ++i) {
    const exprt &s = i->first;
    debug() << "IS(" << pretty_short(s) << ") == {";

    for (expr_sett::const_iterator j = i->second.begin(), end = i->second.end();
         j != end; ++j) 
      debug() << pretty_short (*j) << "; ";
    debug() << "}"  << eom;


    for (expr_sett::const_iterator j = i->second.begin(), end = i->second.end();
         j != end; ++j) {
      const exprt &val = *j;

      for (size_t k = 0; k < universal_axioms.size(); ++k) {
	assert(universal_axioms[k].is_univ_quant());
	string_constraintt lemma = instantiate(universal_axioms[k], s, val);
	assert(lemma.is_simple());
	add_lemma(lemma);
      }
    }
  }
}

exprt string_constraint_generatort::convert_string_to_char_array
(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();  
  assert(args.size() == 1);

  string_exprt str = make_string(args[0]);
  debug() << "convert_string_to_char_array returns: " << str.content().pretty() << eom;
  return str.content();
}





exprt string_constraint_generatort::convert_string_compare_to(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();  
  assert(args.size() == 2);

  string_exprt s1 = make_string(args[0]);
  string_exprt s2 = make_string(args[1]);
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

  symbol_exprt i = string_exprt::fresh_symbol("QA_compare_to",index_type);
  equal_exprt res_null = equal_exprt(res,constant_of_nat(0,return_type));
  string_axioms.emplace_back(res_null, equal_exprt(s1.length(),s2.length()));
  string_axioms.push_back(string_constraintt(res_null,equal_exprt(s1[i],s2[i])).forall(i,zero,s1.length()));
  symbol_exprt x = fresh_index("index_compare_to");
  string_axioms.push_back
    (implies_exprt
     (not_exprt(res_null),
      and_exprt
      (binary_relation_exprt(x,ID_ge,constant_of_nat(0,return_type)),
       or_exprt
       (and_exprt
	(equal_exprt(res,typecast_exprt(minus_exprt(s1[x],s2[x]),return_type)),
	 or_exprt
	 (and_exprt(s1<=s2,s1 > x), and_exprt(s1>=s2,s2 > x))),
	and_exprt
	(equal_exprt(res,typecast_exprt(minus_exprt(s1.length(),s2.length()),return_type)),
	 or_exprt
	 (and_exprt(s2>s1,equal_exprt(x,s1.length())), and_exprt(s1>s2,equal_exprt(x,s2.length()))))))
      ));

  string_axioms.push_back(string_constraintt(not_exprt(res_null),equal_exprt(s1[i],s2[i])).forall(i,zero,x));

  return res;
}

symbol_exprt string_constraint_generatort::convert_string_intern(const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();  
  assert(args.size() == 1);
  string_exprt str = make_string(args[0]);
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
  
  string_axioms.emplace_back(disj);


  // WARNING: the specification may be incomplete or incorrect
  for(it = symbol_to_string.begin(); it != symbol_to_string.end(); it++) 
    if(it->second != str) {
      symbol_exprt i = string_exprt::fresh_symbol("index_intern", refined_string_typet::index_type());
      string_axioms.emplace_back
	(or_exprt
	 (equal_exprt(pool[it->second],pool[str]),
	  or_exprt
	  (not_exprt(equal_exprt(it->second.length(),str.length())),
	   and_exprt(equal_exprt(it->second.length(),str.length()),
		     and_exprt(not_exprt(equal_exprt(str[i],it->second[i])),
			       and_exprt(str>i,binary_relation_exprt(i,ID_ge,zero)))
		     ))));
    }
			

  return pool[str];
}

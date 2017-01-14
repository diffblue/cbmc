/** -*- C++ -*- *****************************************************\

Module: String expressions for PASS algorithm
        (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_expr.h>
#include <ansi-c/string_constant.h>
#include <util/unicode.h>
#include <solvers/floatbv/float_bv.h>
#include <java_bytecode/java_types.h>

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


void string_exprt::of_if(const if_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  assert(refined_string_typet::is_unrefined_string_type(expr.true_case().type()));
  string_exprt t = of_expr(expr.true_case(),symbol_to_string,axioms);
  assert(refined_string_typet::is_unrefined_string_type(expr.false_case().type()));
  string_exprt f = of_expr(expr.false_case(),symbol_to_string,axioms);

  axioms.emplace_back(expr.cond(),equal_exprt(length(),t.length()));
  symbol_exprt qvar = fresh_symbol("string_if_true",refined_string_typet::index_type());
  axioms.push_back(string_constraintt(expr.cond(),equal_exprt((*this)[qvar],t[qvar])).forall(qvar,index_zero,t.length()));
  
  axioms.emplace_back(not_exprt(expr.cond()),equal_exprt(length(),f.length()));
  symbol_exprt qvar2 = fresh_symbol("string_if_false",refined_string_typet::index_type());
  axioms.push_back(string_constraintt(not_exprt(expr.cond()),equal_exprt((*this)[qvar2],f[qvar2])).forall(qvar2,index_zero,f.length()));
}


string_exprt string_exprt::get_string_of_symbol(std::map<irep_idt, string_exprt> & symbol_to_string, const symbol_exprt & sym) {
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

string_exprt string_exprt::of_expr(const exprt & unrefined_string, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  unsignedbv_typet char_type;

  if(refined_string_typet::is_c_string_type(unrefined_string.type())) 
    char_type = refined_string_typet::char_type();
  else
    char_type = refined_string_typet::java_char_type();

  string_exprt s(char_type);
    
  if(unrefined_string.id()==ID_function_application) 
    s.of_function_application(to_function_application_expr(unrefined_string), symbol_to_string,axioms);
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
  else 
    throw ("string_exprt of:\n" + unrefined_string.pretty() 
	   + "\nwhich is not a function application, a symbol or an if expression");

  axioms.emplace_back(s >= index_zero);
  return s;
}

void string_exprt::of_function_application(const function_application_exprt & expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const exprt &name = expr.function();
  if (name.id() == ID_symbol) {
    const irep_idt &id = to_symbol_expr(name).get_identifier();
    if(starts_with(id,cprover_string_literal_func))
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
  throw "string_exprt::of_function_application: not a string function";
}

irep_idt string_exprt::extract_java_string(const symbol_exprt & s){
  std::string tmp(s.get(ID_identifier).c_str());
  std::string value = tmp.substr(31);
  return irep_idt(value);
}

void string_exprt::of_string_constant(irep_idt sval, int char_width, unsignedbv_typet char_type, axiom_vect &axioms){

  std::string str = sval.c_str();
  // should only do this for java
  std::wstring utf16 = utf8_to_utf16be(str);
  // warning: endianness should be used as a flag when using this function
  
  for (std::size_t i = 0; i < utf16.size(); ++i) {
    std::string idx_binary = integer2binary(i,STRING_SOLVER_INDEX_WIDTH);
    constant_exprt idx(idx_binary, refined_string_typet::index_type());
    // warning: this should disappear if utf8_to_utf16 takes into account endianness
    //wchar_t big_endian = ((utf16[i] << 8) & 0xFF00) | (utf16[i] >> 8);

    std::string sval_binary=integer2binary((unsigned)utf16[i], char_width);
    constant_exprt c(sval_binary,char_type);
    equal_exprt lemma(index_exprt(content(), idx), c);
    axioms.emplace_back(lemma,true);
  }
  
  std::string s_length_binary = integer2binary(unsigned(utf16.size()),STRING_SOLVER_INDEX_WIDTH);
  exprt s_length = constant_exprt(s_length_binary, refined_string_typet::index_type());

  axioms.emplace_back(equal_exprt(length(),s_length));
}
				   
void string_exprt::of_empty_string(const function_application_exprt &f, axiom_vect & axioms)
{
  assert(f.arguments().size() == 0); 
  axioms.emplace_back(equal_exprt(length(),index_zero));
}

void string_exprt::of_string_literal(const function_application_exprt &f, axiom_vect & axioms)
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


void string_exprt::of_string_concat(const string_exprt & s1, const string_exprt & s2, axiom_vect & axioms) {
  equal_exprt length_sum_lem(length(), plus_exprt(s1.length(), s2.length()));
  axioms.emplace_back(length_sum_lem);

  symbol_exprt idx = fresh_symbol("QA_index_concat",refined_string_typet::index_type());

  string_constraintt a1(equal_exprt(s1[idx],(*this)[idx]));
  axioms.push_back(a1.forall(idx, index_zero, s1.length()));


  symbol_exprt idx2 = fresh_symbol("QA_index_concat2",refined_string_typet::index_type());

  string_constraintt a2(equal_exprt(s2[idx2],(*this)[plus_exprt(idx2,s1.length())]));
  axioms.push_back(a2.forall(idx2, index_zero, s2.length()));
}

void string_exprt::of_string_concat(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string concat
  
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2 = string_exprt::of_expr(args[1],symbol_to_string,axioms); 

  of_string_concat(s1, s2, axioms);
}



void string_exprt::of_string_copy(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1);
  
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  axioms.emplace_back(equal_exprt(length(), s1.length()));
  symbol_exprt idx = fresh_symbol("QA_index_copy",refined_string_typet::index_type());
  string_constraintt a1(equal_exprt(s1[idx],(*this)[idx]));
  axioms.push_back(a1.forall(idx, index_zero, s1.length()));  
}

void string_exprt::of_string_set_length(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2);

  bool is_c_string = refined_string_typet::is_c_string_type(f.type());
  exprt null_char;
  if(is_c_string)
    null_char = constant_of_nat(0,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
  else 
    null_char = constant_of_nat(0,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
  
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);

  // |s| = k 
  // && forall i < |s|. (i < k ==> s[i] = s1[i]) && (i >= k ==> s[i] = 0)

  axioms.emplace_back(equal_exprt(length(), args[1]));
  symbol_exprt idx = fresh_symbol("QA_index_set_length",refined_string_typet::index_type());

  
  string_constraintt a1
    (and_exprt(implies_exprt(s1 > idx, equal_exprt(s1[idx],(*this)[idx])),
	       implies_exprt(s1 <= idx, equal_exprt(s1[idx],null_char))));
  axioms.push_back(a1.forall(idx, index_zero, (*this).length()));  
}



void string_exprt::of_java_char_array(const exprt & char_array, axiom_vect & axioms)
{
  exprt arr = to_address_of_expr(char_array).object();
  exprt len = member_exprt(arr, "length",length().type());
  exprt cont = member_exprt(arr, "data",content().type());
  op0() = len;
  op1() = cont;
}
 

void string_exprt::of_string_value_of(const function_application_exprt &f, axiom_vect & axioms)
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
      axioms.push_back(a1.forall(idx, index_zero, count));  
    }
  else
    {
      assert(args.size() == 1);
      of_java_char_array(args[0],axioms);
    }
}

void string_exprt::of_string_substring
(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() >= 2);

  string_exprt str = of_expr(args[0],symbol_to_string,axioms);

  exprt i(args[1]);

  exprt j;
  if(args.size() == 3) j = args[2];
  else j = str.length();

  of_string_substring(str,i,j,symbol_to_string,axioms);
}

void string_exprt::of_string_substring
  (const string_exprt & str, const exprt & start, const exprt & end, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  symbol_exprt idx = fresh_symbol("index_substring", refined_string_typet::index_type());
  assert(start.type() == refined_string_typet::index_type());
  assert(end.type() == refined_string_typet::index_type());

  axioms.emplace_back(equal_exprt(length(), minus_exprt(end, start)));
  axioms.emplace_back(binary_relation_exprt(start, ID_lt, end));
  axioms.emplace_back(str >= end);

  // forall idx < str.length, str[idx] = arg_str[idx+i]
  string_constraintt a(equal_exprt((*this)[idx], str[plus_exprt(start, idx)]));
  
  axioms.push_back(a.forall(idx,index_zero,length()));
}

void string_exprt::of_string_trim
(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 1);
  string_exprt str = of_expr(args[0],symbol_to_string,axioms);
  symbol_exprt idx = fresh_symbol("index_trim", refined_string_typet::index_type());

  bool is_c_string = refined_string_typet::is_c_string_type(expr.type());
  exprt space_char;
  if(is_c_string)
    space_char = constant_of_nat(32,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
  else 
    space_char = constant_of_nat(32,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());

  // m + |s1| <= |str|
  axioms.emplace_back(str >= plus_exprt(idx, length()));
  axioms.emplace_back(binary_relation_exprt(idx, ID_ge, index_zero));
  axioms.emplace_back(str >= idx);
  axioms.emplace_back(str >= length());
  ///axioms.emplace_back(binary_relation_exprt(length(), ID_gt, index_zero));

  symbol_exprt n = fresh_symbol("QA_index_trim",refined_string_typet::index_type());
  // forall n < m, str[n] = ' '
  string_constraintt a(equal_exprt(str[n], space_char));
  axioms.push_back(a.forall(n,index_zero,idx));

  symbol_exprt n2 = fresh_symbol("QA_index_trim2",refined_string_typet::index_type());
  // forall n < |str|-m-|s1|, str[m+|s1|+n] = ' '
  string_constraintt a1(equal_exprt(str[plus_exprt(idx,plus_exprt(length(),n2))], space_char));
  axioms.push_back(a1.forall(n2,index_zero,minus_exprt(str.length(),plus_exprt(idx,length()))));

  symbol_exprt n3 = fresh_symbol("QA_index_trim3",refined_string_typet::index_type());
  // forall n < |s1|, s[idx+n] = s1[n]
  string_constraintt a2(equal_exprt((*this)[n3], str[plus_exprt(n3, idx)]));
  axioms.push_back(a2.forall(n3,index_zero,length()));
  // (s[m] != ' ' && s[m+|s1|-1] != ' ') || m = |s|
  or_exprt m_index_condition(equal_exprt(idx,str.length()),
			     and_exprt
			     (not_exprt(equal_exprt(str[idx],space_char)),
			      not_exprt(equal_exprt(str[minus_exprt(plus_exprt(idx,length()),refined_string_typet::index_of_int(1))],space_char))));
  axioms.push_back(m_index_condition);
}

void string_exprt::of_string_to_lower_case
(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 1);

  string_exprt str = of_expr(args[0],symbol_to_string,axioms);
  bool is_c_string = refined_string_typet::is_c_string_type(expr.type());
  exprt char_a;
  exprt char_A;
  exprt char_z;
  exprt char_Z;
  if(is_c_string) {
    char_a = constant_of_nat(97,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
    char_A = constant_of_nat(65,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
    char_z = constant_of_nat(122,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
    char_Z = constant_of_nat(90,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
  } else { 
    char_a = constant_of_nat(97,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
    char_A = constant_of_nat(65,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
    char_z = constant_of_nat(122,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
    char_Z = constant_of_nat(90,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
  }

  axioms.emplace_back(equal_exprt(length(), str.length()));

  symbol_exprt idx = fresh_symbol("QA_lower_case",refined_string_typet::index_type());
  // forall idx < str.length, this[idx] = 'A'<=str[idx]<='Z' ? str[idx]+'a'-'A' : str[idx]
  exprt is_upper_case = and_exprt(binary_relation_exprt(char_A,ID_le,str[idx]),
				  binary_relation_exprt(str[idx],ID_le,char_Z));
  equal_exprt convert((*this)[idx],plus_exprt(str[idx],minus_exprt(char_a,char_A)));
  equal_exprt eq((*this)[idx], str[idx]);
  string_constraintt a(and_exprt(implies_exprt(is_upper_case,convert),implies_exprt(not_exprt(is_upper_case),eq)));
  axioms.push_back(a.forall(idx,index_zero,length()));
}


void string_exprt::of_string_to_upper_case
(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 1);

  string_exprt str = of_expr(args[0],symbol_to_string,axioms);
  bool is_c_string = refined_string_typet::is_c_string_type(expr.type());
  exprt char_a;
  exprt char_A;
  exprt char_z;
  exprt char_Z;

  if(is_c_string) {
    char_a = constant_of_nat(97,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
    char_A = constant_of_nat(65,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
    char_z = constant_of_nat(122,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
    char_Z = constant_of_nat(90,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
  } else { 
    char_a = constant_of_nat(97,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
    char_A = constant_of_nat(65,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
    char_z = constant_of_nat(122,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
    char_Z = constant_of_nat(90,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
  }

  axioms.emplace_back(equal_exprt(length(), str.length()));

  symbol_exprt idx = fresh_symbol("QA_upper_case",refined_string_typet::index_type());
  // forall idx < str.length, this[idx] = 'a'<=str[idx]<='z' ? str[idx]+'A'-'a' : str[idx]
  exprt is_lower_case = and_exprt(binary_relation_exprt(char_a,ID_le,str[idx]),
				  binary_relation_exprt(str[idx],ID_le,char_z));
  equal_exprt convert((*this)[idx],plus_exprt(str[idx],minus_exprt(char_A,char_a)));
  equal_exprt eq((*this)[idx], str[idx]);
  string_constraintt a(and_exprt(implies_exprt(is_lower_case,convert),implies_exprt(not_exprt(is_lower_case),eq)));
  axioms.push_back(a.forall(idx,index_zero,length()));
}


void string_exprt::of_int
(const function_application_exprt &expr,axiom_vect & axioms)
{
  assert(expr.arguments().size() == 1);
  of_int(expr.arguments()[0],axioms,refined_string_typet::is_c_string_type(expr.type()),10);
}

void string_exprt::of_long
(const function_application_exprt &expr,axiom_vect & axioms)
{
  assert(expr.arguments().size() == 1);
  of_int(expr.arguments()[0],axioms,refined_string_typet::is_c_string_type(expr.type()),30);
}


void string_exprt::of_float
(const function_application_exprt &f,axiom_vect & axioms)
{
  assert(f.arguments().size() == 1);
  of_float(f.arguments()[0],axioms,refined_string_typet::is_c_string_type(f.type()),false);
}

void string_exprt::of_float
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
			).forall(qvar,index_zero,nan_string.length()));

  // If the argument is not NaN, the result is a string that represents the sign and magnitude (absolute value) of the argument. If the sign is negative, the first character of the result is '-' ('\u002D'); if the sign is positive, no sign character appears in the result. 

  const bitvector_typet &bv_type=to_bitvector_type(f.type());
  unsigned width=bv_type.get_width();
  exprt isneg = extractbit_exprt(f, width-1);

  axioms.emplace_back(isneg, equal_exprt(sign_string.length(),refined_string_typet::index_of_int(1)));
  
  axioms.emplace_back(not_exprt(isneg), equal_exprt(sign_string.length(),refined_string_typet::index_of_int(0)));
  axioms.emplace_back(isneg,equal_exprt(sign_string[refined_string_typet::index_of_int(0)], constant_of_nat(0x2D,char_width,char_type)));


  // If m is infinity, it is represented by the characters "Infinity"; thus, positive infinity produces the result "Infinity" and negative infinity produces the result "-Infinity".

  string_exprt infinity_string(char_type);
  infinity_string.of_string_constant("Infinity",char_width,char_type,axioms);
  exprt isinf = float_bvt().isinf(f,fspec);
  axioms.emplace_back(isinf, equal_exprt(magnitude.length(),infinity_string.length()));
  symbol_exprt qvar_inf = string_exprt::fresh_symbol("qvar_equal_infinity", refined_string_typet::index_type());
  axioms.push_back
    (string_constraintt(isinf,equal_exprt(magnitude[qvar_inf],infinity_string[qvar_inf])
			).forall(qvar_inf,index_zero,infinity_string.length()));

  //If m is zero, it is represented by the characters "0.0"; thus, negative zero produces the result "-0.0" and positive zero produces the result "0.0".

  string_exprt zero_string(char_type);
  zero_string.of_string_constant("0.0",char_width,char_type,axioms);
  exprt iszero = float_bvt().is_zero(f,fspec);
  axioms.emplace_back(iszero, equal_exprt(magnitude.length(),zero_string.length()));
  symbol_exprt qvar_zero = string_exprt::fresh_symbol("qvar_equal_zero", refined_string_typet::index_type());
  axioms.push_back
    (string_constraintt(iszero,equal_exprt(magnitude[qvar_zero],zero_string[qvar_zero])
			).forall(qvar_zero,index_zero,zero_string.length()));

  
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

void string_exprt::of_double
(const function_application_exprt &f,axiom_vect & axioms)
{
  assert(f.arguments().size() == 1);
  of_float(f.arguments()[0],axioms,refined_string_typet::is_c_string_type(f.type()),true);
}


void string_exprt::of_bool
(const function_application_exprt &f,axiom_vect & axioms)
{
  assert(f.arguments().size() == 1);
  of_bool(f.arguments()[0],axioms,refined_string_typet::is_c_string_type(f.type()));

}

void string_exprt::of_bool
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
			).forall(qvar,index_zero,true_string.length()));

  axioms.emplace_back(not_exprt(eq), equal_exprt(length(),false_string.length()));
  symbol_exprt qvar1 = string_exprt::fresh_symbol("qvar_equal_false", refined_string_typet::index_type());
  axioms.push_back
    (string_constraintt(not_exprt(eq),equal_exprt((*this)[qvar1],false_string[qvar1])
			).forall(qvar,index_zero,false_string.length()));



}


void string_exprt::of_int
(const exprt &i,axiom_vect & axioms,bool is_c_string, int max_size)
{
  typet type = i.type();
  int width = type.get_unsigned_int(ID_width);
  exprt ten = constant_of_nat(10,width,type);
  exprt zero_char;
  exprt nine_char;
  exprt minus_char;

  if(is_c_string) {
    minus_char = constant_of_nat(45,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
    zero_char = constant_of_nat(48,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
    nine_char = constant_of_nat(57,STRING_SOLVER_CHAR_WIDTH,refined_string_typet::char_type());
    } else {     
    minus_char = constant_of_nat(45,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
    zero_char = constant_of_nat(48,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
    nine_char = constant_of_nat(57,JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type());
  }

  axioms.emplace_back(and_exprt(*this > index_zero,*this <= refined_string_typet::index_of_int(max_size)));

  exprt chr = (*this)[refined_string_typet::index_of_int(0)];
  exprt starts_with_minus = equal_exprt(chr,minus_char);
  exprt starts_with_digit = and_exprt
    (binary_relation_exprt(chr,ID_ge,zero_char),
     binary_relation_exprt(chr,ID_le,nine_char));
  axioms.emplace_back(or_exprt(starts_with_digit,starts_with_minus));

  for(int size=1; size<=max_size;size++) {
    exprt sum = constant_of_nat(0,width,type);
    exprt all_numbers = true_exprt();
    chr = (*this)[refined_string_typet::index_of_int(0)];
    exprt first_value = typecast_exprt(minus_exprt(chr,zero_char),type);

    for(int j=1; j<size; j++) {
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
			  not_exprt(equal_exprt((*this)[index_zero],zero_char)));
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


void string_exprt::of_int_hex
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
  axioms.emplace_back(and_exprt(*this > index_zero,*this <= refined_string_typet::index_of_int(max_size)));

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
			  not_exprt(equal_exprt((*this)[index_zero],zero_char)));
    }

  }
}

void string_exprt::of_int_hex
(const function_application_exprt &f,axiom_vect & axioms)
{
  assert(f.arguments().size() == 1);
  of_int_hex(f.arguments()[0],axioms,refined_string_typet::is_c_string_type(f.type()));
}

void string_exprt::of_char
(const function_application_exprt &f,axiom_vect & axioms)
{
  assert(f.arguments().size() == 1);
  of_char(f.arguments()[0],axioms,refined_string_typet::is_c_string_type(f.type()));

}

void string_exprt::of_char
(const exprt &c, axiom_vect & axioms, bool is_c_string)
{
  and_exprt lemma(equal_exprt((*this)[refined_string_typet::index_of_int(0)], c),
		  equal_exprt(length(), refined_string_typet::index_of_int(1)));
  axioms.push_back(lemma);

}


void string_exprt::of_code_point(const exprt &code_point, axiom_vect & axioms, bool is_c_string)
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


void string_exprt::of_string_char_set
(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); //bad args to string_char_set?

  string_exprt str = of_expr(args[0],symbol_to_string,axioms);
  symbol_exprt c = fresh_symbol("char", refined_string_typet::get_char_type(args[0]));
  
  axioms.emplace_back(equal_exprt(c,args[2]));
  with_exprt sarrnew(str.content(), args[1], c);
  implies_exprt lemma(binary_relation_exprt(args[1], ID_lt, str.length()),
                      and_exprt(equal_exprt(content(), sarrnew),
                                equal_exprt(length(), str.length())));
  axioms.push_back(lemma);

}

void string_exprt::of_string_replace
(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = f.arguments();  
  assert(args.size() == 3); 
  string_exprt str = of_expr(args[0],symbol_to_string,axioms);
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
      ).forall(qvar,index_zero,length()));

}

void string_exprt::of_string_delete_char_at
(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 2); 
  string_exprt str = of_expr(args[0],symbol_to_string,axioms);
  exprt index_one = refined_string_typet::index_of_int(1);
  of_string_delete(str,args[1],plus_exprt(args[1],index_one),symbol_to_string,axioms);
}

void string_exprt::of_string_delete
(const string_exprt &str, const exprt & start, const exprt & end, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
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
  str1.of_string_substring(str,index_zero,start,symbol_to_string,axioms);
  str2.of_string_substring(str,end,str.length(),symbol_to_string,axioms);
  of_string_concat(str1,str2,axioms);
  
}

void string_exprt::of_string_delete
(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); 
  string_exprt str = of_expr(args[0],symbol_to_string,axioms);
  of_string_delete(str,args[1],args[2],symbol_to_string,axioms);
}


void string_exprt::of_string_concat_int(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_int(args[1],axioms,refined_string_typet::is_c_string_type(args[0].type()),10);
  of_string_concat(s1,s2,axioms);
}

void string_exprt::of_string_concat_long(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  
  s2.of_int(args[1],axioms,refined_string_typet::is_c_string_type(args[0].type()),30);
  of_string_concat(s1,s2,axioms);
}

void string_exprt::of_string_concat_bool(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_bool(args[1],axioms,refined_string_typet::is_c_string_type(f.type()));
  of_string_concat(s1,s2,axioms);
}

void string_exprt::of_string_concat_char(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_char(args[1],axioms,refined_string_typet::is_c_string_type(f.type()));
  of_string_concat(s1,s2,axioms);
}

void string_exprt::of_string_concat_double(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_float(args[1],axioms,refined_string_typet::is_c_string_type(f.type()),30);
  of_string_concat(s1,s2,axioms);
}

void string_exprt::of_string_concat_float(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_float(args[1],axioms,refined_string_typet::is_c_string_type(f.type()),10);
  of_string_concat(s1,s2,axioms);
}

void string_exprt::of_string_concat_code_point(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_code_point(args[1],axioms,refined_string_typet::is_c_string_type(f.type()));
  of_string_concat(s1,s2,axioms);
}

void string_exprt::of_string_insert(const string_exprt & s1, const string_exprt & s2, 
		      const exprt & offset, 
		      std::map<irep_idt, string_exprt> & symbol_to_string, 
		      axiom_vect & axioms) 
{
  assert(offset.type() == refined_string_typet::index_type());
  unsignedbv_typet char_type = refined_string_typet::get_char_type(s1);
  string_exprt pref(char_type);
  string_exprt suf(char_type);
  string_exprt concat1(char_type);
  pref.of_string_substring(s1,index_zero,offset,symbol_to_string,axioms);
  suf.of_string_substring(s1,offset,s1.length(),symbol_to_string,axioms);
  concat1.of_string_concat(pref,s2,axioms);
  of_string_concat(concat1,suf,axioms);
}


void string_exprt::of_string_insert(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2 = string_exprt::of_expr(args[2],symbol_to_string,axioms); 
  of_string_insert(s1, s2, args[1],symbol_to_string, axioms);
}

void string_exprt::of_string_insert_int(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[2]));
  s2.of_int(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()),10);
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}

void string_exprt::of_string_insert_long(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[2]));
  s2.of_int(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()),30);
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}

void string_exprt::of_string_insert_bool(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_bool(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()));
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}

void string_exprt::of_string_insert_char(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_char(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()));
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}

void string_exprt::of_string_insert_double(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_float(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()),30);
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}

void string_exprt::of_string_insert_float(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 3); 
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2(refined_string_typet::get_char_type(args[0]));
  s2.of_float(args[2],axioms,refined_string_typet::is_c_string_type(args[0].type()),10);
  of_string_insert(s1,s2,args[1],symbol_to_string,axioms);
}


#include <iostream>

void string_exprt::of_string_format(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms){
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

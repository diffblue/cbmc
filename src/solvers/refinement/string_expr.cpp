/** -*- C++ -*- *****************************************************\

Module: String expressions for PASS algorithm
        (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_expr.h>
#include <ansi-c/string_constant.h>

// For debuggin
#include <iostream>

enum {UNDEFINED_MODE, USE_JAVA_STRINGS, USE_C_STRINGS } string_language_mode;

void ensure_java_strings(){
  if(string_language_mode == UNDEFINED_MODE)
    string_language_mode = USE_JAVA_STRINGS;
  assert(string_language_mode == USE_JAVA_STRINGS);
}
    
void ensure_c_strings(){
  if(string_language_mode == UNDEFINED_MODE)
    string_language_mode = USE_C_STRINGS;
  assert(string_language_mode == USE_C_STRINGS);
}

string_ref_typet::string_ref_typet() : struct_typet() {
  components().resize(2);
  components()[0].set_name("length");
  components()[0].set_pretty_name("length");
  components()[0].type()=string_ref_typet::index_type();

  array_typet char_array(string_ref_typet::char_type(),infinity_exprt(string_ref_typet::index_type()));
  components()[1].set_name("content");
  components()[1].set_pretty_name("content");
  components()[1].type()=char_array;
}

string_ref_typet::string_ref_typet(unsignedbv_typet char_type) : struct_typet() {
  components().resize(2);
  components()[0].set_name("length");
  components()[0].set_pretty_name("length");
  components()[0].type()=string_ref_typet::index_type();

  array_typet char_array(char_type,infinity_exprt(string_ref_typet::index_type()));
  components()[1].set_name("content");
  components()[1].set_pretty_name("content");
  components()[1].type()=char_array;
}

exprt index_zero = string_ref_typet::index_zero();
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

bool string_ref_typet::is_c_string_type(const typet &type)
{
  if (type.id() == ID_struct) {
    irep_idt tag = to_struct_type(type).get_tag();
    return (tag == irep_idt("__CPROVER_string"));
  } else return false;
}

bool string_ref_typet::is_java_string_type(const typet &type)
{
  if(type.id() == ID_pointer) {
    pointer_typet pt = to_pointer_type(type);
    typet subtype = pt.subtype();
    if(subtype.id() == ID_struct) {
      irep_idt tag = to_struct_type(subtype).get_tag();
      return (tag == irep_idt("java.lang.String"));
    } else return false;
  } else return false;
}

string_exprt::string_exprt() : struct_exprt(string_ref_typet())
{
  string_ref_typet t;
  if(string_language_mode == USE_JAVA_STRINGS)
    t = string_ref_typet(string_ref_typet::java_char_type());
  symbol_exprt length = fresh_symbol("string_length",string_ref_typet::index_type());
  symbol_exprt content = fresh_symbol("string_content",t.get_content_type());
  move_to_operands(length,content);
}

string_exprt::string_exprt(unsignedbv_typet char_type) : struct_exprt(string_ref_typet())
{
  string_ref_typet t(char_type);
  if(char_type == string_ref_typet::java_char_type())
    ensure_java_strings();
  symbol_exprt length = fresh_symbol("string_length",string_ref_typet::index_type());
  symbol_exprt content = fresh_symbol("string_content",t.get_content_type());
  move_to_operands(length,content);
}

/*
std::map<irep_idt, string_exprt> symbol_to_string_exprt;

std::map<irep_idt, string_exprt> string_exprt::symbol_to_string(){
return symbol_to_string_exprt;
};

string_exprt string_exprt::find_symbol(const symbol_exprt & expr){
  return symbol_to_string_exprt[expr.get_identifier()];
}

void string_exprt::assign_to_symbol(const symbol_exprt & expr){
symbol_to_string_exprt[expr.get_identifier()] = *this;
}*/

void string_exprt::of_if(const if_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  assert(string_ref_typet::is_unrefined_string_type(expr.true_case().type()));
  string_exprt t = of_expr(expr.true_case(),symbol_to_string,axioms);
  assert(string_ref_typet::is_unrefined_string_type(expr.false_case().type()));
  string_exprt f = of_expr(expr.false_case(),symbol_to_string,axioms);

  axioms.emplace_back(implies_exprt(expr.cond(),equal_exprt(length(),t.length())));
  symbol_exprt qvar = fresh_symbol("string_if",string_ref_typet::index_type());
  axioms.push_back(string_constraintt(expr.cond(),equal_exprt((*this)[qvar],t[qvar])).forall(qvar,index_zero,t.length()));
;
 axioms.emplace_back(implies_exprt(not_exprt(expr.cond()),equal_exprt(length(),f.length())));
symbol_exprt qvar2 = fresh_symbol("string_if",string_ref_typet::index_type());
  axioms.push_back(string_constraintt(not_exprt(expr.cond()),equal_exprt((*this)[qvar],f[qvar])).forall(qvar2,index_zero,f.length()));
}

string_exprt string_exprt::of_expr(const exprt & unrefined_string, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  string_exprt s;
  if(string_ref_typet::is_java_string_type(unrefined_string.type()))
    s = string_exprt(string_ref_typet::java_char_type());

  if(unrefined_string.id()==ID_function_application) 
    s.of_function_application(to_function_application_expr(unrefined_string), symbol_to_string,axioms);
  else if(unrefined_string.id()==ID_symbol) 
    s = symbol_to_string[to_symbol_expr(unrefined_string).get_identifier()];
  else if(unrefined_string.id()==ID_nondet_symbol) 
    s = symbol_to_string[unrefined_string.get(ID_identifier)];
  else if(unrefined_string.id()==ID_address_of) {
    assert(unrefined_string.op0().id()==ID_symbol);
    s = symbol_to_string[to_symbol_expr(unrefined_string.op0()).get_identifier()];
  }
  else if(unrefined_string.id()==ID_if) 
    s.of_if(to_if_expr(unrefined_string),symbol_to_string,axioms);
  else if(unrefined_string.id()==ID_struct) 
    s.of_struct(to_struct_expr(unrefined_string),symbol_to_string,axioms);
  else 
    throw ("string_exprt of:\n" + unrefined_string.pretty() 
	   + "\nwhich is not a function application, a symbol of an if expression");

  axioms.emplace_back(s >= index_zero);
  return s;
}


void string_exprt::of_struct(const struct_exprt & expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  // Warning: we do nothing here!!!!
  return;
}

void string_exprt::of_function_application(const function_application_exprt & expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const exprt &name = expr.function();
  if (name.id() == ID_symbol) {
    const irep_idt &id = to_symbol_expr(name).get_identifier();
    //std::cout << "string_exprt::of_function_application(" 
    //<< id << ")" << std::endl;
    if (is_string_literal_func(id)) {
      return of_string_literal(expr,axioms);
    } else if (is_string_concat_func(id)) {
      return of_string_concat(expr,symbol_to_string,axioms);
    } else if (is_string_substring_func(id)) {
      return of_string_substring(expr,symbol_to_string,axioms);
    } else if (is_string_char_set_func(id)) {
      return of_string_char_set(expr,symbol_to_string,axioms);
    } 
  }
  throw "non string function";
}

irep_idt string_exprt::extract_java_string(const symbol_exprt & s){
  std::string tmp(s.get(ID_identifier).c_str());
  std::string value = tmp.substr(31);
  std::cout << "of_string_litteral: " << value << std::endl;
  return irep_idt(value);
}

void string_exprt::of_string_constant(irep_idt sval, int char_width, unsignedbv_typet char_type, axiom_vect &axioms){
  for (std::size_t i = 0; i < sval.size(); ++i) {
    std::string idx_binary = integer2binary(i,INDEX_WIDTH);
    constant_exprt idx(idx_binary, string_ref_typet::index_type());
    std::string sval_binary=integer2binary(unsigned(sval[i]), char_width);
    constant_exprt c(sval_binary,char_type);
    equal_exprt lemma(index_exprt(content(), idx), c);
    axioms.emplace_back(lemma);
  }
  
  std::string s_length_binary = integer2binary(unsigned(sval.size()),INDEX_WIDTH);
  exprt s_length = constant_exprt(s_length_binary, string_ref_typet::index_type());

  axioms.emplace_back(equal_exprt(length(),s_length));
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
    char_width = CHAR_WIDTH;
    char_type = string_ref_typet::char_type();

  } else {
    // Java string constant
    assert (arg.operands().size() == 1); 
    assert(string_ref_typet::is_unrefined_string_type(arg.type()));
    const exprt &s = arg.op0();
    
    std::cout << "it seems the value of the string is lost, " 
	      << "we need to recover it from the identifier" << std::endl;
    /*std::string tmp(s.get(ID_identifier).c_str());
    std::string value = tmp.substr(31);
    std::cout << "of_string_litteral: " << value << std::endl;*/
    sval = extract_java_string(to_symbol_expr(s));
    char_width = JAVA_CHAR_WIDTH;
    char_type = string_ref_typet::java_char_type();
  }

  of_string_constant(sval,char_width,char_type,axioms);
}


void string_exprt::of_string_concat(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string concat
  
  string_exprt s1 = string_exprt::of_expr(args[0],symbol_to_string,axioms);
  string_exprt s2 = string_exprt::of_expr(args[1],symbol_to_string,axioms);

  equal_exprt length_sum_lem(length(), plus_exprt(s1.length(), s2.length()));
  axioms.emplace_back(length_sum_lem);
  // We can run into problems if the length of the string exceed 32 bits?
  //binary_relation_exprt lem1(length(), ID_ge, s1.length());
  //axioms.push_back(string_constraintt(lem1));
  //binary_relation_exprt lem2(length(), ID_ge, s2.length());
  //axioms.push_back(string_constraintt(lem2));

  symbol_exprt idx = fresh_symbol("QA_index_concat",string_ref_typet::index_type());

  string_constraintt a1(equal_exprt(s1[idx],(*this)[idx]));
  axioms.push_back(a1.forall(idx, index_zero, s1.length()));


  symbol_exprt idx2 = fresh_symbol("QA_index_concat2",string_ref_typet::index_type());

  string_constraintt a2(equal_exprt(s2[idx2],(*this)[plus_exprt(idx2,s1.length())]));
  axioms.push_back(a2.forall(idx2, index_zero, s2.length()));
  
}

void string_exprt::of_string_substring
(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); // bad args to string substring?

  string_exprt str = of_expr(args[0],symbol_to_string,axioms);
  exprt i(args[1]);
  assert(i.type() == string_ref_typet::index_type());
  exprt j(args[2]);
  assert(j.type() == string_ref_typet::index_type());

  symbol_exprt idx = fresh_symbol("index_substring", string_ref_typet::index_type());

  axioms.emplace_back(equal_exprt(length(), minus_exprt(j, i)));
  axioms.emplace_back(binary_relation_exprt(i, ID_lt, j));
  axioms.emplace_back(str >= j);

  // forall idx < str.length, str[idx] = arg_str[idx+i]
  string_constraintt a(equal_exprt(index_exprt(content(),idx), 
				   str[plus_exprt(i, idx)]));
  
  axioms.push_back(a.forall(idx,index_zero,length()));
}

void string_exprt::of_string_char_set
(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); //bad args to string_char_set?

  string_exprt str = of_expr(args[0],symbol_to_string,axioms);
  symbol_exprt c = fresh_symbol("char", string_ref_typet::char_type());
  
  //THIS HAS NOT BEEN CHECKED:  
  axioms.emplace_back(equal_exprt(c,args[2]));
  with_exprt sarrnew(str.content(), args[1], c);
  implies_exprt lemma(binary_relation_exprt(args[1], ID_lt, str.length()),
                      and_exprt(equal_exprt(content(), 
					    // update_exprt(str.content(), args[1], c)),
					    sarrnew),
                                equal_exprt(length(), str.length())));
  axioms.push_back(lemma);

}


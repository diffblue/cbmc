/** -*- C++ -*- *****************************************************\

Module: String support via axiom instantiation
        (see the PASS paper at HVC'13)

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

#include <solvers/refinement/string_refinement.h>
#include <ansi-c/string_constant.h>
#include <util/i2string.h>
#include <util/replace_expr.h>
#include <solvers/sat/satcheck.h>
#include <sstream>


// This is mostly for debugging:
#include <langapi/languages.h>
#include <ansi-c/ansi_c_language.h>
#include <iostream>

// Types used in this refinement
unsignedbv_typet char_type(CHAR_WIDTH);
//unsignedbv_typet index_type(INDEX_WIDTH);
signedbv_typet index_type(INDEX_WIDTH);

constant_exprt index_of_int(int i) {
  return constant_exprt(integer2binary(i, INDEX_WIDTH), index_type);
}

constant_exprt zero = index_of_int(0);


// associate a string to symbols
std::map<irep_idt, string_exprt> symbol_to_string;

string_ref_typet::string_ref_typet() : struct_typet() {
  components().resize(2);

  components()[0].set_name("length");
  components()[0].set_pretty_name("length");
  components()[0].type()=index_type;

  array_typet char_array(char_type,infinity_exprt(index_type));
  components()[1].set_name("content");
  components()[1].set_pretty_name("content");
  components()[1].type()=char_array;
}


// Succinct version of pretty()
std::string string_refinementt::pretty_short(const exprt & expr) {
  languagest languages(ns, new_ansi_c_language());
  std::string string_value;
  languages.from_expr(expr, string_value);
  return string_value;
}


std::string string_refinementt::constraint_to_string(const string_constraintt & sc) {
  if(sc.is_simple()) return(pretty_short(sc));
  else if(sc.is_univ_quant())
    return ("forall " + pretty_short(sc.get_univ_var()) + ". (" 
	    + pretty_short(sc));
  else
    return "forall QA. exists QE s1 != s2 ...";
}



string_refinementt::string_refinementt(const namespacet &_ns, propt &_prop):
  SUB(_ns, _prop)
{
  use_counter_example = false;
  witness_bound = 2;
  variable_with_multiple_occurence_in_index = false;
  initial_loop_bound = 10;

  string_literal_func = "__CPROVER_uninterpreted_string_literal";
  char_literal_func = "__CPROVER_uninterpreted_char_literal";
  string_length_func = "__CPROVER_uninterpreted_strlen";
  string_equal_func = "__CPROVER_uninterpreted_string_equal";
  string_copy_func = "__CPROVER_uninterpreted_string_copy";
  string_char_at_func = "__CPROVER_uninterpreted_char_at";
  string_concat_func = "__CPROVER_uninterpreted_strcat";
  string_substring_func = "__CPROVER_uninterpreted_substring";
  string_is_prefix_func = "__CPROVER_uninterpreted_strprefixof";
  string_is_suffix_func = "__CPROVER_uninterpreted_strsuffixof";
  string_contains_func = "__CPROVER_uninterpreted_strcontains";
  string_char_set_func = "__CPROVER_uninterpreted_char_set";
  string_index_of_func = "__CPROVER_uninterpreted_strindexof";
  string_last_index_of_func = "__CPROVER_uninterpreted_strlastindexof";
}

string_refinementt::~string_refinementt()
{
}

bool string_refinementt::is_unrefined_string_type(const typet &type)
{
  if (type.id() == ID_struct) {
    irep_idt tag = to_struct_type(type).get_tag();
    return tag == irep_idt("__CPROVER_string");
  }
  return false;
}

bool string_refinementt::is_unrefined_char_type(const typet &type)
{
/*if (type.id() == ID_struct) {
  irep_idt tag = to_struct_type(type).get_tag();
  return tag == irep_idt("__CPROVER_char");
  }
  return false;*/
  return (type == char_type);
}

unsigned string_refinementt::next_symbol_id = 1;

symbol_exprt string_refinementt::fresh_symbol(const irep_idt &prefix,
                                              const typet &tp)
{
  std::ostringstream buf;
  buf << "string_refinement#" << prefix << "#" << (next_symbol_id++);
  std::string s = buf.str();
  irep_idt name(s.c_str());
  return symbol_exprt(name, tp);
}

string_exprt::string_exprt() : struct_exprt(string_ref_typet())
{
  string_ref_typet t;
  symbol_exprt length = string_refinementt::fresh_symbol("string_length",index_type);
  symbol_exprt content = string_refinementt::fresh_symbol("string_content",t.get_content_type());
  move_to_operands(length,content);
}

string_exprt string_exprt::find_symbol(const symbol_exprt & expr){
  return symbol_to_string[expr.get_identifier()];
}

void string_exprt::of_if(const if_exprt &expr, axiom_vect & axioms)
{
  assert(string_refinementt::is_unrefined_string_type(expr.true_case().type()));
  string_exprt t = of_expr(expr.true_case(),axioms);
  assert(string_refinementt::is_unrefined_string_type(expr.false_case().type()));
  string_exprt f = of_expr(expr.false_case(),axioms);

  axioms.emplace_back(implies_exprt(expr.cond(),equal_exprt(length(),t.length())));
  symbol_exprt qvar = string_refinementt::fresh_symbol("string_if",index_type);
  axioms.push_back(string_constraintt(expr.cond(),equal_exprt((*this)[qvar],t[qvar])).forall(qvar,zero,t.length()));
;
 axioms.emplace_back(implies_exprt(not_exprt(expr.cond()),equal_exprt(length(),f.length())));
  symbol_exprt qvar2 = string_refinementt::fresh_symbol("string_if",index_type);
  axioms.push_back(string_constraintt(not_exprt(expr.cond()),equal_exprt((*this)[qvar],f[qvar])).forall(qvar2,zero,f.length()));
}

string_exprt string_exprt::of_expr(const exprt & unrefined_string, axiom_vect & axioms)
{
  string_exprt s;
  if(unrefined_string.id()==ID_function_application) 
    s.of_function_application(to_function_application_expr(unrefined_string), axioms);
  else if(unrefined_string.id()==ID_symbol) 
    s = find_symbol(to_symbol_expr(unrefined_string));
  else if(unrefined_string.id()==ID_if) 
    s.of_if(to_if_expr(unrefined_string),axioms);
  else 
    throw ("string_exprt of:\n" + unrefined_string.pretty() 
	   + "\nwhich is not a symbol or a function application");

  axioms.emplace_back(string_refinementt::is_positive(s.length()));
  return s;
}

exprt string_exprt::within_bounds(const exprt & idx, const exprt & bound)
{
  return and_exprt(binary_relation_exprt(idx, ID_ge, index_of_int(0)),
		   binary_relation_exprt(idx, ID_lt, bound));
}

void string_exprt::of_function_application(const function_application_exprt & expr, axiom_vect & axioms)
{
  const exprt &name = expr.function();
  if (name.id() == ID_symbol) {
    const irep_idt &id = to_symbol_expr(name).get_identifier();
    //std::cout << "string_exprt::of_function_application(" 
    //<< id << ")" << std::endl;
    if (id == "__CPROVER_uninterpreted_string_literal") {
      return of_string_literal(expr,axioms);
    } else if (id == "__CPROVER_uninterpreted_strcat") {
      return of_string_concat(expr,axioms);
    } else if (id == "__CPROVER_uninterpreted_substring") {
      return of_string_substring(expr,axioms);
    } else if (id == "__CPROVER_uninterpreted_char_set") {
      return of_string_char_set(expr,axioms);
    } 
  }
  throw "non string function";
}
					   
void string_exprt::of_string_literal(const function_application_exprt &f, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); //bad args to string literal?
  const exprt &arg = args[0];

  assert (arg.operands().size() == 1 &&
	  arg.op0().operands().size() == 1 &&
	  arg.op0().op0().operands().size() == 2 &&
	  arg.op0().op0().op0().id() == ID_string_constant); // bad arg to string literal?
      
  const exprt &s = arg.op0().op0().op0();
  irep_idt sval = to_string_constant(s).get_value();

  for (std::size_t i = 0; i < sval.size(); ++i) {
    std::string idx_binary = integer2binary(i,INDEX_WIDTH);
    constant_exprt idx(idx_binary, index_type);
    std::string sval_binary=integer2binary(unsigned(sval[i]), CHAR_WIDTH);
    constant_exprt c(sval_binary,char_type);
    equal_exprt lemma(index_exprt(content(), idx), c);
    axioms.emplace_back(lemma);
  }

  std::string s_length_binary = integer2binary(unsigned(sval.size()),INDEX_WIDTH);
  exprt s_length = constant_exprt(s_length_binary, index_type);

  axioms.emplace_back(equal_exprt(length(),s_length));
}


void string_exprt::of_string_concat(const function_application_exprt &f, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string concat
  
  string_exprt s1 = string_exprt::of_expr(args[0],axioms);
  string_exprt s2 = string_exprt::of_expr(args[1],axioms);

  equal_exprt length_sum_lem(length(), plus_exprt(s1.length(), s2.length()));
  axioms.emplace_back(length_sum_lem);
  // We can run into problems if the length of the string exceed 32 bits?
  //binary_relation_exprt lem1(length(), ID_ge, s1.length());
  //axioms.push_back(string_constraintt(lem1));
  //binary_relation_exprt lem2(length(), ID_ge, s2.length());
  //axioms.push_back(string_constraintt(lem2));

  symbol_exprt idx = string_refinementt::fresh_symbol("QA_index_concat",index_type);

  string_constraintt a1(equal_exprt(s1[idx],(*this)[idx]));
  axioms.push_back(a1.forall(idx, zero, s1.length()));


  symbol_exprt idx2 = string_refinementt::fresh_symbol("QA_index_concat2",index_type);

  string_constraintt a2(equal_exprt(s2[idx2],(*this)[plus_exprt(idx2,s1.length())]));
  axioms.push_back(a2.forall(idx2, zero, s2.length()));
  
}

void string_exprt::of_string_substring
(const function_application_exprt &expr, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); // bad args to string substring?

  string_exprt str = of_expr(args[0],axioms);
  exprt i(args[1]);
  assert(i.type() == index_type);
  exprt j(args[2]);
  assert(j.type() == index_type);

  symbol_exprt idx = string_refinementt::fresh_symbol("index_substring", index_type);

  axioms.emplace_back(equal_exprt(length(), minus_exprt(j, i)));
  axioms.emplace_back(binary_relation_exprt(i, ID_lt, j));
  axioms.emplace_back(str >= j);

  // forall idx < str.length, str[idx] = arg_str[idx+i]
  string_constraintt a(equal_exprt(index_exprt(content(),idx), 
				   str[plus_exprt(i, idx)]));
  
  axioms.push_back(a.forall(idx,zero,length()));
}

void string_exprt::of_string_char_set
(const function_application_exprt &expr,axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); //bad args to string_char_set?

  string_exprt str = of_expr(args[0],axioms);
  symbol_exprt c = string_refinementt::fresh_symbol("char", char_type);
  
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



///////////////////////
// String refinement //
///////////////////////


// We add instantiations before launching the solver
void string_refinementt::post_process()
{  
  //debug() << "string_refinementt::post_process()" << eom;
  std::vector<string_constraintt> new_axioms;
  for(int i = 0; i < string_axioms.size(); i++)
    if(string_axioms[i].is_simple())
      add_implies_lemma(string_axioms[i].premise(),string_axioms[i].body());
    else if(string_axioms[i].is_univ_quant())
      new_axioms.push_back(string_axioms[i]);
    else 
      not_contains_axioms.push_back(string_axioms[i]);

  string_axioms = new_axioms;
  //add_instantiations(true);

  nb_sat_iteration = 0;

  update_index_set(string_axioms);
  update_index_set(cur); 
  cur.clear();
  add_instantiations();
  // We should check at each step whether the lemmas are satisfiable or not
  //  while(!index_set.empty()) {cur.clear();   add_instantiations();    index_set.clear();     update_index_set(cur);   }

  while(!current_index_set.empty() && initial_loop_bound-- > 0 && !variable_with_multiple_occurence_in_index)
    {
      current_index_set.clear(); 
      update_index_set(cur); 
      cur.clear();
      add_instantiations();
    }

  debug()<< "post_process: " << initial_loop_bound << " steps skipped" << eom;
  SUB::post_process();
}

literalt string_refinementt::convert_rest(const exprt &expr)
{
  if(expr.id()==ID_function_application)
    {
      bvt bv = convert_function_application(to_function_application_expr(expr));
      assert(bv.size() == 1); 
      return bv[0];
    }
  else
    return SUB::convert_rest(expr);
}


bool string_refinementt::boolbv_set_equality_to_true(const equal_exprt &expr)
{
  if(!equality_propagation) return true;

  const typet &type=ns.follow(expr.lhs().type());

  if(expr.lhs().id()==ID_symbol &&
     type==ns.follow(expr.rhs().type()) &&
     type.id()!=ID_bool)
  {
    if(is_unrefined_string_type(type)) {
      symbol_exprt sym = to_symbol_expr(expr.lhs());
      make_string(sym,expr.rhs());
      return false;
    }
    else if(is_unrefined_char_type(type)) {
      const bvt &bv1=convert_bv(expr.rhs());
      symbol_exprt sym = to_symbol_expr(expr.lhs());
      const irep_idt &identifier = sym.get_identifier();
      map.set_literals(identifier, char_type, bv1);
      if(freeze_all) set_frozen(bv1);
      return false;
    } else return SUB::boolbv_set_equality_to_true(expr);
  }

  return true;
}

bvt string_refinementt::convert_symbol(const exprt &expr)
{
  const typet &type = expr.type();
  const irep_idt &identifier = expr.get(ID_identifier);
  if(identifier.empty())
    throw "string_refinementt::convert_symbol got empty identifier";

  if (is_unrefined_string_type(type)) {
    //debug() << "string_refinementt::convert_symbol of unrefined string" << eom;
    // this can happen because of boolbvt::convert_equality
    string_exprt str = string_exprt::find_symbol(to_symbol_expr(expr));
    bvt bv = convert_bv(str);
    return bv;
  } else if (is_unrefined_char_type(expr.type())) {
    bvt bv;
    bv.resize(CHAR_WIDTH);
    map.get_literals(identifier, char_type, CHAR_WIDTH, bv);

    forall_literals(it, bv)
      if(it->var_no()>=prop.no_variables() && !it->is_constant())
	{
	  error() << identifier << eom;
	  assert(false);
	}
    return bv;
  } else return SUB::convert_symbol(expr);
}


bvt string_refinementt::convert_function_application(
       const function_application_exprt &expr)
{
  const exprt &name = expr.function();

  if (name.id() == ID_symbol) {
    const irep_idt &id = to_symbol_expr(name).get_identifier();
    //debug() << "string_refinementt::convert_function_application(" 
    // << id << ")" << eom;
    if (id == string_literal_func 
	|| id == string_concat_func 
	|| id == string_substring_func
	|| id == string_char_set_func) {
      string_exprt str = make_string(expr);
      bvt bv = convert_bv(str);
      return bv;
    } else if (id == char_literal_func) {
      return convert_char_literal(expr);
    } else if (id == string_length_func) {
      return convert_string_length(expr);
    } else if (id == string_equal_func) {
      return convert_string_equal(expr);
    } else if (id == string_char_at_func) {
      return convert_string_char_at(expr);
    } else if (id == string_is_prefix_func) {
      return convert_string_is_prefix(expr);
    } else if (id == string_is_suffix_func) {
      return convert_string_is_suffix(expr);
    } else if (id == string_contains_func) {
      return convert_string_contains(expr);
    } else if (id == string_index_of_func) {
      return convert_string_index_of(expr);
    } else if (id == string_last_index_of_func) {
      return convert_string_last_index_of(expr);
    }
  }

  return SUB::convert_function_application(expr);
}

bool just_checked_axiom = false;

void string_refinementt::check_SAT()
{
  SUB::check_SAT();

  if(!progress){
  /*    if(just_checked_axiom)
      {
	current_index_set.clear(); 
	update_index_set(cur); 
	if(current_index_set.empty())
	  debug() << "inconclusive: the model is not correct but there is nothing to add the index set" << eom;
	progress=(!current_index_set.empty());
	cur.clear();
	add_instantiations();
	just_checked_axiom = false;
      }
      else{*/
    if(!check_axioms()) {
      //just_checked_axiom = true;
      //progress = true;
      debug() << "check_SAT: warning, got sat but the model is not correct" << eom;
      progress = false;
    } 
    else
      progress = false;
  }
  //} 
}

bvt string_refinementt::convert_bool_bv(const exprt &boole, const exprt &orig)
{
  bvt ret;
  ret.push_back(convert(boole));
  size_t width = boolbv_width(orig.type());
  for (size_t i = 1; i < width; ++i) {
    ret.push_back(const_literal(false));
  }
  return ret;
}

void string_refinementt::add_lemma(const exprt &lemma)
{
  debug() << "adding lemma " << pretty_short(lemma) << eom;

  prop.l_set_to_true(convert(lemma));
  cur.push_back(lemma);
  all_lemmas.insert(lemma);
}

void string_refinementt::add_again_lemmas() {
  for(expr_sett::iterator it = all_lemmas.begin(); it != all_lemmas.end(); it++)
    prop.l_set_to_true(convert(*it));
}


void string_refinementt::add_implies_lemma(const exprt &prem, const exprt & body)
{
  if (!seen_instances.insert(implies_exprt(prem,body)).second)
    return;

  if(body == true_exprt()) return; // tautology
  
  satcheck_no_simplifiert sat_check;
  SUB solver(ns, sat_check);
  solver << prem;

  switch (solver()) {
  case decision_proceduret::D_UNSATISFIABLE:
    debug() << "add_implies_lemma: precondition unsatisfiable" << eom;
    break;
  case decision_proceduret::D_SATISFIABLE: 
  default:
    if(prem  == true_exprt()) 
      add_lemma(body);
    else
      add_lemma(implies_exprt(prem,body));
  }
  /*
  if(prem  == true_exprt()) 
    add_lemma(body);
  else
  add_lemma(implies_exprt(prem,body));*/
}

void string_refinementt::make_string(const symbol_exprt & sym, const exprt & str) 
{
  if(str.id()==ID_symbol) 
    symbol_to_string[sym.get_identifier()] = 
      string_exprt::find_symbol(to_symbol_expr(str));
  else
    symbol_to_string[sym.get_identifier()] = 
      string_exprt::of_expr(str,string_axioms);
}

string_exprt string_refinementt::make_string(const exprt & str) 
{
  if(str.id()==ID_symbol) 
    return string_exprt::find_symbol(to_symbol_expr(str));
  else
    return string_exprt::of_expr(str,string_axioms);
}

bvt string_refinementt::convert_string_equal(
  const function_application_exprt &f)
{
  assert(f.type() == bool_typet()); 
  symbol_exprt eq = fresh_boolean("equal");
  bvt bv = convert_bv(eq);

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
  symbol_exprt qvar = fresh_symbol("qvar_equal", index_type);

  string_axioms.emplace_back(eq, equal_exprt(s1.length(), s2.length()));

  string_axioms.push_back
    (string_constraintt(eq,equal_exprt(s1[qvar],s2[qvar])
			).forall(qvar,zero,s1.length()));

  string_axioms.emplace_back
    (not_exprt(eq),
     or_exprt(notequal_exprt(s1.length(), s2.length()),
	      and_exprt(string_exprt::within_bounds(witness,s1.length()),
			notequal_exprt(s1[witness],s2[witness]))));

  return bv;
}


bvt string_refinementt::convert_string_length(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); //bad args to string length?
  string_exprt str = make_string(args[0]);
  exprt length = str.length();
  bvt bv = convert_bv(length);
  return bv;
}

exprt string_refinementt::is_positive(const exprt & x)
{ return binary_relation_exprt(x, ID_ge, index_of_int(0)); }


bvt string_refinementt::convert_string_is_prefix(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string isprefix

  symbol_exprt isprefix = fresh_boolean("isprefix");
  string_exprt s0 = make_string(args[0]);
  string_exprt s1 = make_string(args[1]);
  assert(f.type() == bool_typet());
  bvt bv = convert_bv(isprefix); 

  string_axioms.emplace_back(implies_exprt(isprefix, s1 >= s0));

  symbol_exprt qvar = fresh_symbol("QA_isprefix", index_type);
  string_axioms.push_back
    (string_constraintt(isprefix, equal_exprt(s0[qvar],s1[qvar])
			).forall(qvar,zero,s0.length()));
	     
  symbol_exprt witness = fresh_index("witness_not_isprefix");

  // forall witness < s0.length. isprefix => s0[witness] = s2[witness]

  or_exprt s0_notpref_s1(not_exprt(s1 >= s0),
			 and_exprt(s0 > witness, 
				   notequal_exprt(s0[witness],s1[witness])));
		       
  string_axioms.emplace_back(implies_exprt (not_exprt(isprefix),and_exprt(is_positive(witness),s0_notpref_s1)));
  return bv;
}


bvt string_refinementt::convert_string_is_suffix(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string issuffix?

  symbol_exprt issuffix = fresh_boolean("issuffix");
  string_exprt s0 = make_string(args[0]);
  string_exprt s1 = make_string(args[1]);


  // issufix(s1,s0) => s0.length >= s1.length
  // && forall witness < s1.length. 
  //     issufix => s1[witness] = s0[witness + s0.length - s1.length]
  // && !issuffix => s1.length > s0.length 
  //       || (s1.length > witness && s1[witness] != s0[witness + s0.length - s1.length]

  string_axioms.emplace_back(implies_exprt(issuffix, s1 >= s0));

  symbol_exprt qvar = fresh_symbol("QA_suffix", index_type);
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

  assert(f.type() == bool_typet());
  bvt bv = convert_bv(issuffix);

  return bv;
}


bvt string_refinementt::convert_string_contains(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string contains?

  symbol_exprt contains = fresh_boolean("contains");
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

  symbol_exprt qvar = fresh_symbol("QA_contains", index_type);
  exprt qvar_shifted = plus_exprt(qvar, startpos);
  string_axioms.push_back
    (string_constraintt(contains,equal_exprt(s1[qvar],s0[qvar_shifted])
			).forall(qvar,zero,s1.length()));

  // We rewrite the axiom for !contains as:
  // forall startpos <= |s0| - |s1|.  (!contains && |s0| >= |s1| )
  //      ==> exists witness < |s1|. s1[witness] != s0[startpos+witness]

  string_axioms.push_back
    (string_constraintt::not_contains
     (zero,plus_exprt(index_of_int(1),minus_exprt(s0.length(),s1.length())), 
      and_exprt(not_exprt(contains),s0 >= s1),zero,s1.length(),s0,s1));

  assert(f.type() == bool_typet());
  return convert_bv(contains);
}


symbol_exprt string_refinementt::fresh_index(const irep_idt &prefix){
  symbol_exprt i = fresh_symbol(prefix,index_type);
  index_symbols.push_back(i);
  return i;
}

symbol_exprt string_refinementt::fresh_boolean(const irep_idt &prefix){
  symbol_exprt b = fresh_symbol(prefix,bool_typet());
  boolean_symbols.push_back(b);
  return b;
}

bvt string_refinementt::convert_string_index_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string index of?

  symbol_exprt index = fresh_index("index_of");
  string_exprt str = make_string(args[0]);
  exprt c = args[1];
  assert(is_unrefined_char_type(c.type()));
  // (i = -1 || 0 <= i < s && s[i] = c) && forall n. n < i => s[n] != c 
  
  string_axioms.push_back((string_constraintt(str > index) && is_positive(index)) || equal_exprt(index,index_of_int(-1)));

  symbol_exprt n = fresh_symbol("QA_index_of",index_type);

  string_axioms.push_back((! string_constraintt(equal_exprt(str[n],c))).forall(n,zero,index));

  bvt bv = convert_bv(index);
  return bv;
}

bvt string_refinementt::convert_string_last_index_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string last index of?

  symbol_exprt index = fresh_index("last_index_of");
  bvt bv = convert_bv(index);
  return bv;
}

bvt string_refinementt::convert_char_literal(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); // there should be exactly 1 argument to char literal

  const exprt &arg = args[0];
  // argument to char literal should be one string constant of size one
  assert(arg.operands().size() == 1 &&
	 arg.op0().operands().size() == 1 &&
	 arg.op0().op0().operands().size() == 2 &&
	 arg.op0().op0().op0().id() == ID_string_constant); 

  const string_constantt s = to_string_constant(arg.op0().op0().op0());
  irep_idt sval = s.get_value();
  assert(sval.size() == 1); 

  std::string binary=integer2binary(unsigned(sval[0]), CHAR_WIDTH);

  return convert_bv(constant_exprt(binary, char_type));
}


bvt string_refinementt::convert_string_char_at(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //string_char_at expects 2 arguments
  string_exprt str = make_string(args[0]);
  debug() << "in convert_string_char_at: we add the index to the"
	  << " index set" << eom;

  symbol_exprt char_sym = fresh_symbol("char",char_type);
  string_axioms.emplace_back(equal_exprt(char_sym,str[args[1]]));
  return convert_bv(char_sym);
}



// We compute the index set for all formulas, instantiate the formulas
// with the found indexes, and add them as lemmas.
void string_refinementt::add_instantiations()
{
  debug() << "string_refinementt::add_instantiations: "
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

      for (size_t k = 0; k < string_axioms.size(); ++k) {
	assert(string_axioms[k].is_univ_quant());
	string_constraintt lemma = instantiate(string_axioms[k], s, val);
	assert(lemma.is_simple());
	add_implies_lemma(lemma.premise(),lemma.body());
      }
    }
  }
}


unsigned integer_of_expr(const constant_exprt & expr) {
  return integer2unsigned(string2integer(as_string(expr.get_value()),2));
}

std::string string_refinementt::string_of_array(const exprt &arr, const exprt &size)
{
  unsigned n = integer_of_expr(to_constant_expr(size));
  if(n>500) return "very long string";
  if(n==0) return "\"\"";
  unsigned str[n];
  exprt val = get(arr);
  if(val.id() == "array-list") {
    for (size_t i = 0; i < val.operands().size()/2; i++) {  
      exprt index = val.operands()[i*2];
      unsigned idx = integer_of_expr(to_constant_expr(index));
      if(idx < n){
	exprt value = val.operands()[i*2+1];
	str[idx] = integer_of_expr(to_constant_expr(value));
      }
    }
  } else {
    return "unable to get array-list";
  }

  std::ostringstream buf;
  buf << "\"";
  for(unsigned i = 0; i < n; i++) {
    char c = (char) str[i];
    if(31<c)
      buf << c ;
    else
      buf << "?";
  }
  
  buf << "\"";
  return buf.str();
}

exprt string_refinementt::get_array(const exprt &arr, const exprt &size)
{
  //debug() << "string_refinementt::get_array(" << arr.get(ID_identifier) 
  //	  << "," << size.get(ID_value) << ")" << eom;
  exprt val = get(arr);
  
  if(val.id() == "array-list") {
    exprt ret =
      array_of_exprt(char_type.zero_expr(), array_typet(char_type, infinity_exprt(index_type)));
    // size));
    
    for (size_t i = 0; i < val.operands().size()/2; i++) {  
      exprt index = val.operands()[i*2];
      assert(index.type() == index_type);
      exprt value = val.operands()[i*2+1];
      assert(value.type() == char_type);
      ret = with_exprt(ret, index, value);
    }
    return ret;
  
  } else {
    debug() << "unable to get array-list value of " 
	    << pretty_short(val) << eom;
    return arr;
  }
}
 

bool string_refinementt::check_axioms()
{
  // build the interpretation from the model of the prop_solver
  
  debug() << "string_refinementt::check_axioms: ==============="
	  << "===========================================" << eom;
  debug() << "string_refinementt::check_axioms: build the" 
	  << " interpretation from the model of the prop_solver" << eom;
  replace_mapt fmodel;

  std::map<irep_idt, string_exprt>::iterator it;
  for (it = symbol_to_string.begin(); it != symbol_to_string.end(); ++it) 
    {
      string_exprt refined = it->second;
      const exprt &econtent = refined.content();
      const exprt &elength  = refined.length();
      
      exprt len = get(elength);
      exprt arr = get_array(econtent, len);

      fmodel[elength] = len;
      fmodel[econtent] = arr;
      debug() << it->first << " = " << pretty_short(it->second) 
	      << " of length " << pretty_short(len) <<" := " << eom
	      << pretty_short(get(econtent)) << eom 
	      << string_of_array(econtent,len) << eom;
    }

  for(std::vector<symbol_exprt>::iterator it = boolean_symbols.begin();
      it != boolean_symbols.end(); it++) {
    debug() << "" << it->get_identifier() << " := " << pretty_short(get(*it)) << eom;  
    fmodel[*it] = get(*it);
  }

  for(std::vector<symbol_exprt>::iterator it = index_symbols.begin();
      it != index_symbols.end(); it++) {
    debug() << "" << it->get_identifier() << " := " << pretty_short(get(*it)) << eom;  
    fmodel[*it] = get(*it);
  }

  debug() << "in check axiom, the model may be incomplete" << eom;
  std::vector< std::pair<size_t, exprt> > violated;

  debug() << "there are " << string_axioms.size() << " string axioms" << eom;
  for (size_t i = 0; i < string_axioms.size(); ++i) {
    const string_constraintt &axiom = string_axioms[i];

    exprt negaxiom = and_exprt(axiom.premise(), not_exprt(axiom.body()));
    replace_expr(fmodel, negaxiom);

    debug() << "negaxiom: " << pretty_short(negaxiom) << eom;

    satcheck_no_simplifiert sat_check;
    SUB solver(ns, sat_check);
    solver << negaxiom;

    switch (solver()) {
    case decision_proceduret::D_SATISFIABLE: {
      exprt val = solver.get(axiom.get_univ_var());
      violated.push_back(std::make_pair(i, val));
    } break;
    case decision_proceduret::D_UNSATISFIABLE:
      break;
    default:
      throw "failure in checking axiom";
    }
  }

  if (violated.empty()) {
    debug() << "no violated property" << eom;
    return true;
  }
  else {
    debug() << violated.size() << " string axioms can be violated" << eom;

    if(use_counter_example) {
      
      std::vector<string_constraintt> new_axioms(violated.size());
      
      // Checking if the current solution satisfies the constraints
      for (size_t i = 0; i < violated.size(); ++i) {
	
	new_axioms[i] = string_axioms[violated[i].first];
	debug() << " axiom " << i <<" "<< constraint_to_string(new_axioms[i]) << eom;
	const exprt &val = violated[i].second;
	const string_constraintt &axiom = string_axioms[violated[i].first];
	
	exprt premise(axiom.premise());
	exprt body(axiom.body());
	implies_exprt instance(premise, body);
	debug() << "warning: we don't eliminate the existential quantifier" << eom;
	replace_expr(axiom.get_univ_var(), val, instance);
	if (seen_instances.insert(instance).second) {
	  add_implies_lemma(premise,body);
	} else debug() << "instance already seen" << eom;
	// TODO - add backwards instantiations
      }
    }

    return false;
  }
  
}


namespace {


  // Gets the upper bounds that are applied to [qvar], in the expression [expr]
  void get_bounds(const exprt &qvar, const exprt &expr, std::vector<exprt> & out)
  {
    std::vector<exprt> to_treat;
    to_treat.push_back(expr);
    while(!to_treat.empty()) {
      exprt e = to_treat.back();
      to_treat.pop_back();
      if (e.id() == ID_lt && e.op0() == qvar) {
	assert(e.op1().type() == index_type || e.op1().type() == integer_typet());
	out.push_back(minus_exprt(e.op1(), index_of_int(1)));
      } else if (e.id() == ID_le && e.op0() == qvar) {
	out.push_back(e.op1());
      } else {
	forall_operands(it, e) {
	  to_treat.push_back(*it);
	}
      }
    }
  }

} // namespace



std::map< exprt, int> string_refinementt::map_of_sum(const exprt &f) {
  // number of time the element should be added (can be negative)
  std::map< exprt, int> elems;

  std::vector< std::pair<exprt, bool> > to_process;
  to_process.push_back(std::make_pair(f, true));

  while (!to_process.empty()) {
    exprt cur = to_process.back().first;
    bool positive = to_process.back().second;
    to_process.pop_back();
    if (cur.id() == ID_plus) {
      to_process.push_back(std::make_pair(cur.op1(), positive));
      to_process.push_back(std::make_pair(cur.op0(), positive));
    } else if (cur.id() == ID_minus) {
      to_process.push_back(std::make_pair(cur.op1(), !positive));
      to_process.push_back(std::make_pair(cur.op0(), positive));
    } else if (cur.id() == ID_unary_minus) {
      to_process.push_back(std::make_pair(cur.op0(), !positive));
    } else {
      if(positive) elems[cur] = elems[cur]+1;
      else elems[cur] = elems[cur] - 1;
    }
  }
  return elems;
}


exprt string_refinementt::sum_of_map(std::map<exprt,int> & m, bool negated) {
  exprt sum = index_of_int(0);

  for (std::map<exprt,int>::iterator it = m.begin();
       it != m.end(); it++) {
    const exprt &t = it->first;
    int second = negated?(-it->second):it->second;
    if (second != 0)
      if (second == -1) 
	if(sum == index_of_int(0)) sum = unary_minus_exprt(t);
	else sum = minus_exprt(sum,t);
      else if (second == 1)
	if(sum == index_of_int(0)) sum = t;
	else sum = plus_exprt(sum, t);
      else {
	debug() << "in string_refinementt::sum_of_map:"
		<< " warning: several occurences of the same variable " << eom;
	variable_with_multiple_occurence_in_index = true;
	if(second > 1)
	  for(int i = 0; i < second; i++)
	    sum = plus_exprt(sum, t);
	else
	  for(int i = 0; i > second; i--)
	    sum = minus_exprt(sum, t);
      }
  }
  return sum;
}

exprt string_refinementt::simplify_sum(const exprt &f) {
  std::map<exprt,int> map = map_of_sum(f);
  return sum_of_map(map);
}

exprt string_refinementt::compute_subst(const exprt &qvar, const exprt &val, const exprt &f) //, exprt & positive, exprt & negative)
{
  exprt positive, negative;
  // number of time the element should be added (can be negative)
  // qvar has to be equal to val - f(0) if it appears positively in f 
  // (ie if f(qvar) = f(0) + qvar) and f(0) - val if it appears negatively 
  // in f. So we start by computing val - f(0).
  std::map< exprt, int> elems = map_of_sum(minus_exprt(val,f));

  bool found = false;
  bool neg = false; // true if qvar appears negatively in f, ie positively in the elements

  for (std::map<exprt,int>::iterator it = elems.begin();
       it != elems.end(); it++) {
    const exprt &t = it->first;
    if (t == qvar) {
      if(it->second == 1 || it->second == -1){
	found = true;
	neg = (it->second == 1);
      } else {
	debug() << "in string_refinementt::compute_subst:"
		<< " warning: occurences of qvar canceled out " << eom;
	assert(it->second == 0);
      }
      elems.erase(it);
    }
  }
  
  
  if (!found) { 
    // we should add a lemma to say that val == f
    debug() << "not sure we need to add a lemma: to say val == f" << eom;
    add_lemma(equal_exprt(val,f));
    return qvar;
  }

  return sum_of_map(elems,neg);
}
  


class find_qvar_visitor: public const_expr_visitort {
private:
  const exprt &qvar_;

public:
  find_qvar_visitor(const exprt &qvar): qvar_(qvar) {}

  void operator()(const exprt &expr) {
    if (expr == qvar_) throw true;
  }
};

// Look for the given symbol in the index expression
bool find_qvar(const exprt index, const symbol_exprt & qvar) {
  find_qvar_visitor v2(qvar);
  try {
    index.visit(v2);
    return false;
  } catch (bool found) {return found;}
}


void string_refinementt::update_index_set(const axiom_vect & string_axioms) {
  for (size_t i = 0; i < string_axioms.size(); ++i) {
    update_index_set(string_axioms[i]);
  }
}

void string_refinementt::update_index_set(const std::vector<exprt> & cur) {
  for (size_t i = 0; i < cur.size(); ++i) {
    update_index_set(cur[i]);
  }
}

void string_refinementt::update_index_set(const string_constraintt &axiom)
{
  debug() << "string_refinementt::update_index_set needs to be rewriten" << eom;
  assert(axiom.is_univ_quant());
  std::vector<exprt> bounds;
  get_bounds(axiom.get_univ_var(), axiom.premise(), bounds);

  std::vector<exprt> to_process;
  to_process.push_back(axiom.body());
  while (!to_process.empty()) {
    exprt cur = to_process.back();
    to_process.pop_back();
    if (cur.id() == ID_index) {
      const exprt &s = cur.op0();
      const exprt &i = cur.op1();

      bool has_quant_var = find_qvar(i,axiom.get_univ_var());

      // if cur is of the form s[i] and no quantified variable appears in i
      if(!has_quant_var){
	if(s.type() == string_type.get_content_type()){
	  expr_sett &idxs = index_set[s];
	  idxs.insert(bounds.begin(), bounds.end());
	  idxs.insert(i);
	  current_index_set[s].insert(bounds.begin(), bounds.end());
	  current_index_set[s].insert(i);
	} else {
	  debug() << "update_index_set: index expression of non string" << eom;
	}
      }
    } else {
      forall_operands(it, cur) {
        to_process.push_back(*it);
      }
    }
  }
}


void string_refinementt::update_index_set(const exprt &formula)
{
  debug() << "string_refinementt::update_index_set needs to be rewriten" << eom;
  std::vector<exprt> to_process;
  to_process.push_back(formula);

  while (!to_process.empty()) {
    exprt cur = to_process.back();
    to_process.pop_back();
    if (cur.id() == ID_index) {
      const exprt &s = cur.op0();
      const exprt &i = cur.op1();
      if(s.type() == string_type.get_content_type()){
	const exprt &simplified = simplify_sum(i);
	if(index_set[s].insert(simplified).second)
	  current_index_set[s].insert(simplified);
      } else {
	debug() << "update_index_set: index expression of non string" << eom;
      }
    } else {
      forall_operands(it, cur) {
        to_process.push_back(*it);
      }
    }
  }
}


// Will be used to visit an expression and return the index used 
// with the given char array
class find_index_visitor: public const_expr_visitort {
private:
    const exprt &str_;
  
public:
  find_index_visitor(const exprt &str): str_(str){}
  
  void operator()(const exprt &expr) {
    if (expr.id() == ID_index) {
      const index_exprt &i = to_index_expr(expr);
      if (i.array() == str_)
	throw i.index();
    }
  }
};

// Find an index used in the char array  str
exprt find_index(const exprt & expr, const exprt & str) {
  find_index_visitor v1(str);
  try {
    expr.visit(v1);
    return nil_exprt();
  } 
  catch (exprt i) { return i; }
}



string_constraintt string_refinementt::instantiate(const string_constraintt &axiom,
				     const exprt &str, const exprt &val)
{
  assert(axiom.is_univ_quant());
  exprt idx = find_index(axiom.body(),str);
  if(idx.is_nil()) return string_constraintt();
  if(!find_qvar(idx,axiom.get_univ_var())) return string_constraintt();

  exprt r = compute_subst(axiom.get_univ_var(), val, idx);
  exprt instance(axiom);
  replace_expr(axiom.get_univ_var(), r, instance);
  return string_constraintt(instance);     
}


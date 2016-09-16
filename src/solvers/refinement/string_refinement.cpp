/** -*- C++ -*- *****************************************************\

Module: String support via axiom instantiation
        (see the PASS paper at HVC'13)

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

#include <ansi-c/string_constant.h>
#include <util/i2string.h>
#include <util/replace_expr.h>
#include <solvers/sat/satcheck.h>
#include <sstream>
#include <solvers/refinement/string_refinement.h>


// This is mostly for debugging:
#include <langapi/languages.h>
#include <ansi-c/ansi_c_language.h>
#include <chrono>


unsignedbv_typet char_type = refined_string_typet::char_type();
signedbv_typet index_type = refined_string_typet::index_type();
unsignedbv_typet java_char_type = refined_string_typet::java_char_type();
constant_exprt zero = refined_string_typet::index_of_int(0);

// Succinct version of pretty()
std::string string_refinementt::pretty_short(const exprt & expr) {
  languagest languages(ns, new_ansi_c_language());
  std::string string_value;
  languages.from_expr(expr, string_value);
  return string_value;
}

string_refinementt::string_refinementt(const namespacet &_ns, propt &_prop):
  SUB(_ns, _prop)
{
  use_counter_example = false;
  variable_with_multiple_occurence_in_index = false;
  initial_loop_bound = 100;
}

void string_refinementt::display_index_set() {
  for (std::map<exprt, expr_sett>::iterator i = index_set.begin(),
	 end = index_set.end(); i != end; ++i) {
    const exprt &s = i->first;
    debug() << "IS(" << pretty_short(s) << ") == {";
    
    for (expr_sett::const_iterator j = i->second.begin(), end = i->second.end();
         j != end; ++j) 
      debug() << pretty_short (*j) << "; ";
    debug() << "}"  << eom;
  }
}


std::chrono::high_resolution_clock::time_point start_time = std::chrono::high_resolution_clock::now();



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
  std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

  auto duration = std::chrono::duration_cast<std::chrono::microseconds>(t1-start_time).count();

  debug() << "string_refinementt::boolbv_set_equality_to_true time in ms: " 
	  << (duration / 1000) << eom;

  if(!equality_propagation) return true;

  const typet &type=ns.follow(expr.lhs().type());

  if(expr.lhs().id()==ID_symbol &&
     type==ns.follow(expr.rhs().type()) &&
     type.id()!=ID_bool)
  {
    if(refined_string_typet::is_unrefined_string_type(type)) {
      symbol_exprt sym = to_symbol_expr(expr.lhs());
      make_string(sym,expr.rhs());
      return false;
    }
    else if(refined_string_typet::is_java_deref_string_type(type)) {
      debug() << "string_refinementt::boolbv_set_equality_to_true: warning"
	      << " non pointer string " << eom;
      symbol_exprt sym = to_symbol_expr(expr.lhs());
      make_string(sym,expr.rhs());
      return false;
    }
    else if(type == char_type) {
      const bvt &bv1=convert_bv(expr.rhs());
      symbol_exprt sym = to_symbol_expr(expr.lhs());
      const irep_idt &identifier = sym.get_identifier();
      map.set_literals(identifier, char_type, bv1);
      if(freeze_all) set_frozen(bv1);
      return false;
    } 
    else if(type == java_char_type) {
      const bvt &bv1=convert_bv(expr.rhs());
      symbol_exprt sym = to_symbol_expr(expr.lhs());
      const irep_idt &identifier = sym.get_identifier();
      map.set_literals(identifier, java_char_type, bv1);
      if(freeze_all) set_frozen(bv1);
      return false;
    } 
    else { 
      return SUB::boolbv_set_equality_to_true(expr);
    }
  }

  return true;
}

bvt string_refinementt::convert_symbol(const exprt &expr)
{
  const typet &type = expr.type();
  const irep_idt &identifier = expr.get(ID_identifier);
  if(identifier.empty())
    throw "string_refinementt::convert_symbol got empty identifier";

  if (refined_string_typet::is_unrefined_string_type(type)) {
    debug() << "string_refinementt::convert_symbol of unrefined string" << eom;
    // this can happen because of boolbvt::convert_equality
    string_exprt str = string_of_symbol(to_symbol_expr(expr));
    bvt bv = convert_bv(str);
    return bv;
  } else if (expr.type() == char_type) {
    bvt bv;
    bv.resize(STRING_SOLVER_CHAR_WIDTH);
    map.get_literals(identifier, char_type, STRING_SOLVER_CHAR_WIDTH, bv);

    forall_literals(it, bv)
      if(it->var_no()>=prop.no_variables() && !it->is_constant())
	{
	  error() << identifier << eom;
	  assert(false);
	}
    return bv;
  } else if (expr.type() == java_char_type) {
    bvt bv;
    bv.resize(JAVA_STRING_SOLVER_CHAR_WIDTH);
    map.get_literals(identifier, java_char_type, JAVA_STRING_SOLVER_CHAR_WIDTH, bv);

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
    debug() << "string_refinementt::convert_function_application(" 
	    << id << ")" << eom;
    if (is_string_literal_func(id)
	|| is_string_concat_func(id)
	|| is_string_substring_func(id)
	|| is_string_char_set_func(id)) {
      string_exprt str = make_string(expr);
      bvt bv = convert_bv(str);
      return bv;
    } else if (is_char_literal_func(id)) {
      return convert_char_literal(expr);
    } else if (is_string_length_func(id)) {
      return convert_string_length(expr);
    } else if (is_string_equal_func(id)) {
      return convert_bv(convert_string_equal(expr));
    } else if (is_string_char_at_func(id)) {
      return convert_string_char_at(expr);
    } else if (is_string_is_prefix_func(id)) {
      return convert_string_is_prefix(expr);
    } else if (is_string_is_suffix_func(id)) {
      return convert_string_is_suffix(expr);
    } else if (is_string_startswith_func(id)) {
      return convert_string_is_prefix(expr,true);
    } else if (is_string_endswith_func(id)) {
      return convert_string_is_suffix(expr,true);
    } else if (is_string_contains_func(id)) {
      return convert_string_contains(expr);
    } else if (is_string_index_of_func(id)) {
      return convert_string_index_of(expr);
    } else if (is_string_last_index_of_func(id)) {
      return convert_string_last_index_of(expr);
    } else if (is_string_parse_int_func(id)) {
      return convert_bv(convert_string_parse_int(expr));
    }
  }

  return SUB::convert_function_application(expr);
}


void string_refinementt::print_time(std::string s) {
  debug() << s << " TIME == "
	  << (std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::high_resolution_clock::now()-start_time).count()  / 1000) << eom;
}

// We add instantiations before launching the solver
void string_refinementt::post_process()
{  
  print_time("post_process");
  for(int i = 0; i < string_axioms.size(); i++)
    if(string_axioms[i].is_simple())
      add_lemma(string_axioms[i]);
    else if(string_axioms[i].is_univ_quant())
      universal_axioms.push_back(string_axioms[i]);
    else {
      assert(string_axioms[i].is_not_contains());
      string_axioms[i].witness = string_exprt::fresh_symbol
	("not_contains_witness",
	 array_typet(refined_string_typet::index_type(),
		     infinity_exprt(refined_string_typet::index_type())));
      not_contains_axioms.push_back(string_axioms[i]);
    }

  string_axioms.clear();

  /*
  debug() << not_contains_axioms.size() << " not_contains constraints" << eom;
  nb_sat_iteration = 0;
  debug() << "string_refinementt::post_process  at step" << step++ << " time in ms "
	  << (std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::high_resolution_clock::now()-start_time).count()  / 1000) << eom;

  debug() << "string_refinementt::post_process: warning update_index_set has to be checked" << eom;
  update_index_set(universal_axioms);
  update_index_set(cur); 
  cur.clear();
  add_instantiations();
  debug() << "string_refinementt::post_process  at step" << step++ << " time in ms "
	  << (std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::high_resolution_clock::now()-start_time).count()  / 1000) << eom;
  */

  SUB::post_process();
}

decision_proceduret::resultt string_refinementt::dec_solve()
{

  debug() << "string_refinementt::post_process: warning update_index_set has to be checked" << eom;
  update_index_set(universal_axioms);
  update_index_set(cur); 
  cur.clear();
  add_instantiations();

  while(initial_loop_bound-- > 0)
    {
      print_time("string_refinementt::dec_solve");
      decision_proceduret::resultt res = SUB::dec_solve();
      
      switch(res) 
	{
	case D_SATISFIABLE:
	  if(!check_axioms()) {
	    debug() << "check_SAT: got SAT but the model is not correct" << eom;
	  } 
	  else {
	    debug() << "check_SAT: the model is correct" << eom;
	    return D_SATISFIABLE;
	  }
	  
	  debug() <<  "refining.." << eom;
	  current_index_set.clear(); 
	  update_index_set(cur); 
	  cur.clear();
	  add_instantiations();
	  
	  if(variable_with_multiple_occurence_in_index)
	    return D_ERROR;
	  
	  if(current_index_set.empty()){
	    debug() << "current index set is empty" << eom;
	    return D_SATISFIABLE;
	  } 

	  display_index_set();
	  debug()<< "instantiating NOT_CONTAINS constraints" << eom;
	  for(int i=0; i<not_contains_axioms.size(); i++) {
	    debug()<< "constraint " << i << eom;
	    std::vector<exprt> lemmas;
	    instantiate_not_contains(not_contains_axioms[i],lemmas);
	    for(int j=0; j<lemmas.size(); j++) {
	      add_lemma(lemmas[j]);
	    }
	  }
	  break;
	default: 
	  return res;
	}


    } 
  debug () << "string_refinementt::dec_solve reached the maximum number of steps allowed";
  return D_ERROR;
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
  if (!seen_instances.insert(lemma).second) return;

  if(lemma == true_exprt()) { debug() << "string_refinementt::add_lemma : tautology" << eom; return; }

  debug() << "adding lemma " << pretty_short(lemma) << eom;

  prop.l_set_to_true(convert(lemma));
  cur.push_back(lemma);
}



string_exprt string_refinementt::string_of_symbol(const symbol_exprt & sym){
  if(refined_string_typet::is_java_string_type(sym.type()) 
     && starts_with(std::string(sym.get(ID_identifier).c_str()),"java::java.lang.String.Literal.")) {
    string_exprt s;
    s.of_string_constant(string_exprt::extract_java_string(sym),JAVA_STRING_SOLVER_CHAR_WIDTH,refined_string_typet::java_char_type(),string_axioms);
    return s;
  }
  else {
    return string_exprt::get_string_of_symbol(symbol_to_string,sym);
  }
}  


void string_refinementt::make_string(const symbol_exprt & sym, const exprt & str) 
{
  if(str.id()==ID_symbol) 
    assign_to_symbol(sym,string_of_symbol(to_symbol_expr(str)));
  else
    assign_to_symbol(sym,string_exprt::of_expr(str,symbol_to_string,string_axioms));
}

string_exprt string_refinementt::make_string(const exprt & str) 
{
  if(str.id()==ID_symbol) 
    return string_of_symbol(to_symbol_expr(str));
  else
    return string_exprt::of_expr(str,symbol_to_string,string_axioms);
}

exprt string_refinementt::convert_string_equal(const function_application_exprt &f) {
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


bvt string_refinementt::convert_string_length(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 1); //bad args to string length?
  string_exprt str = make_string(args[0]);
  exprt length = str.length();
  return convert_bv(length);
}

exprt string_refinementt::is_positive(const exprt & x)
{ return binary_relation_exprt(x, ID_ge, refined_string_typet::index_of_int(0)); }


bvt string_refinementt::convert_string_is_prefix
(const function_application_exprt &f, bool swap_arguments)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string isprefix
  assert(f.type() == bool_typet() || f.type().id() == ID_c_bool);

  symbol_exprt isprefix = fresh_boolean("isprefix");
  typecast_exprt tc_isprefix(isprefix,f.type());
  string_exprt s0 = make_string(args[swap_arguments?1:0]);
  string_exprt s1 = make_string(args[swap_arguments?0:1]);

  string_axioms.emplace_back(isprefix, s1 >= s0);

  symbol_exprt qvar = string_exprt::fresh_symbol("QA_isprefix", index_type);
  string_axioms.push_back
    (string_constraintt(isprefix, equal_exprt(s0[qvar],s1[qvar])
			).forall(qvar,zero,s0.length()));
	     
  symbol_exprt witness = fresh_index("witness_not_isprefix");

  // forall witness < s0.length. isprefix => s0[witness] = s2[witness]

  or_exprt s0_notpref_s1(not_exprt(s1 >= s0),
			 and_exprt(is_positive(witness),
				   and_exprt(s0 > witness, 
					     notequal_exprt(s0[witness],s1[witness]))));
		       
  string_axioms.emplace_back(implies_exprt (not_exprt(isprefix),s0_notpref_s1));


  return convert_bv(tc_isprefix); 
}


bvt string_refinementt::convert_string_is_suffix
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

  return convert_bv(tc_issuffix);
}


bvt string_refinementt::convert_string_contains(
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

  return convert_bv(tc_contains);
}


symbol_exprt string_refinementt::fresh_index(const irep_idt &prefix){
  symbol_exprt i = string_exprt::fresh_symbol(prefix,index_type);
  index_symbols.push_back(i);
  return i;
}

symbol_exprt string_refinementt::fresh_boolean(const irep_idt &prefix){
  symbol_exprt b = string_exprt::fresh_symbol(prefix,bool_typet());
  boolean_symbols.push_back(b);
  return b;
}

bvt string_refinementt::convert_string_index_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string index of?
  if(f.type() != index_type) {
    debug() << "convert_string_index_of of the wrong type "<< f.type().pretty() << eom;
    assert(false);
  }
    
  symbol_exprt index = fresh_index("index_of");
  symbol_exprt contains = fresh_boolean("contains_in_index_of");
  string_exprt str = make_string(args[0]);
  exprt c = args[1];

  if(!(c.type() == char_type || c.type() == java_char_type)){
    debug() << "warning: argument to string_index_of does not have char type: " 
	    << c.type().pretty() << eom;    
    c = typecast_exprt(c,java_char_type);
  }

  // 0 <= i < |s| && (i = -1 <=> !contains) && (contains => s[i] = c)
  // && forall n. 0 < n < i => s[n] != c 
  
  string_axioms.push_back(string_constraintt(equal_exprt(index,refined_string_typet::index_of_int(-1)),not_exprt(contains)).exists(index,refined_string_typet::index_of_int(-1),str.length()));
  string_axioms.emplace_back(not_exprt(contains),equal_exprt(index,refined_string_typet::index_of_int(-1)));
  string_axioms.emplace_back(contains,and_exprt(binary_relation_exprt(zero,ID_le,index),equal_exprt(str[index],c)));


  symbol_exprt n = string_exprt::fresh_symbol("QA_index_of",index_type);

  string_axioms.push_back(string_constraintt(contains,not_exprt(equal_exprt(str[n],c))).forall(n,zero,index));

  symbol_exprt m = string_exprt::fresh_symbol("QA_index_of",index_type);

  string_axioms.push_back(string_constraintt(not_exprt(contains),not_exprt(equal_exprt(str[m],c))).forall(m,zero,str.length()));

  bvt bv = convert_bv(index);
  return bv;
}

bvt string_refinementt::convert_string_last_index_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string last index of?

  symbol_exprt index = fresh_index("last_index_of");
  symbol_exprt contains = fresh_boolean("contains_in_index_of");
  string_exprt str = make_string(args[0]);
  exprt c = args[1];
  if(!(c.type() == char_type || c.type() == java_char_type)){
    debug() << "warning: argument to string_index_of does not have char type: " 
	    << c.type().pretty() << eom;    
    c = typecast_exprt(c,java_char_type);
  }

  string_axioms.push_back(string_constraintt(equal_exprt(index,refined_string_typet::index_of_int(-1)),not_exprt(contains)).exists(index,refined_string_typet::index_of_int(-1),str.length()));
  string_axioms.emplace_back(not_exprt(contains),equal_exprt(index,refined_string_typet::index_of_int(-1)));
  string_axioms.emplace_back(contains,and_exprt(binary_relation_exprt(zero,ID_le,index),equal_exprt(str[index],c)));
  
  symbol_exprt n = string_exprt::fresh_symbol("QA_last_index_of",index_type);
  string_axioms.push_back(string_constraintt(contains,not_exprt(equal_exprt(str[n],c))).forall(n,plus_exprt(index,refined_string_typet::index_of_int(1)),str.length()));

  symbol_exprt m = string_exprt::fresh_symbol("QA_last_index_of",index_type);
  string_axioms.push_back(string_constraintt(not_exprt(contains),not_exprt(equal_exprt(str[m],c))).forall(m,zero,str.length()));

  bvt bv = convert_bv(index);
  return bv;
}

bvt string_refinementt::convert_char_literal(
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
    
    return convert_bv(constant_exprt(binary, char_type));
  }
  else {
    throw "convert_char_literal unimplemented";
  }
    
}


bvt string_refinementt::convert_string_char_at(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //string_char_at expects 2 arguments
  string_exprt str = make_string(args[0]);
  debug() << "in convert_string_char_at: we add the index to the"
	  << " index set" << eom;

  if(f.type() == char_type) {
    symbol_exprt char_sym = string_exprt::fresh_symbol("char",char_type);
    string_axioms.emplace_back(equal_exprt(char_sym,str[args[1]]));
    return convert_bv(char_sym);
  } else {
    assert(f.type() == java_char_type);
    symbol_exprt char_sym = string_exprt::fresh_symbol("char",java_char_type);
    string_axioms.emplace_back(equal_exprt(char_sym,str[args[1]]));
    return convert_bv(char_sym);
  }
}

constant_exprt string_refinementt::constant_of_nat(int i,typet t) {
  return constant_exprt(integer2binary(i, boolbv_width(t)), t);
}

exprt string_refinementt::convert_string_parse_int
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

      for (size_t k = 0; k < universal_axioms.size(); ++k) {
	assert(universal_axioms[k].is_univ_quant());
	string_constraintt lemma = instantiate(universal_axioms[k], s, val);
	assert(lemma.is_simple());
	add_lemma(lemma);
      }
    }
  }
}


unsigned integer_of_expr(const constant_exprt & expr) {
  return integer2unsigned(string2integer(as_string(expr.get_value()),2));
}

std::string string_refinementt::string_of_array(const exprt &arr, const exprt &size)
{
  if(size.id() != ID_constant) return "string of unknown size";
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
  exprt val = get(arr);
  unsignedbv_typet chart;
  if(arr.type().subtype() == char_type)
    chart = char_type;
  else { 
    assert(arr.type().subtype() == java_char_type);
    chart = java_char_type;
  }

  if(val.id() == "array-list") {
    exprt ret =
      array_of_exprt(chart.zero_expr(), array_typet(chart, infinity_exprt(index_type)));
    
    for (size_t i = 0; i < val.operands().size()/2; i++) {  
      exprt index = val.operands()[i*2];
      assert(index.type() == index_type);
      exprt value = val.operands()[i*2+1];
      assert(value.type() == char_type || value.type() == java_char_type);
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

  debug() << "there are " << universal_axioms.size() << " universal axioms" << eom;
  for (size_t i = 0; i < universal_axioms.size(); ++i) {
    const string_constraintt &axiom = universal_axioms[i];

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


  debug() << "there are " << not_contains_axioms.size() << " not_contains axioms" << eom;
  for (size_t i = 0; i < not_contains_axioms.size(); ++i) {
    exprt val = get(not_contains_axioms[i].witness_of(zero));
    violated.push_back(std::make_pair(i, val));
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
	
	new_axioms[i] = universal_axioms[violated[i].first];

	const exprt &val = violated[i].second;
	const string_constraintt &axiom = universal_axioms[violated[i].first];
	
	exprt premise(axiom.premise());
	exprt body(axiom.body());
	implies_exprt instance(premise, body);
	debug() << "warning: we don't eliminate the existential quantifier" << eom;
	replace_expr(axiom.get_univ_var(), val, instance);
	if (seen_instances.insert(instance).second) {
	  add_lemma(instance);
	} else debug() << "instance already seen" << eom;
      }
    }

    return false;
  }
  
}


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
	out.push_back(minus_exprt(e.op1(), refined_string_typet::index_of_int(1)));
      } else if (e.id() == ID_le && e.op0() == qvar) {
	out.push_back(e.op1());
      } else {
	forall_operands(it, e) {
	  to_treat.push_back(*it);
	}
      }
    }
  }



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
  exprt sum = refined_string_typet::refined_string_typet::index_of_int(0);

  for (std::map<exprt,int>::iterator it = m.begin();
       it != m.end(); it++) {
    const exprt &t = it->first;
    int second = negated?(-it->second):it->second;
    if (second != 0)
      if (second == -1) 
	if(sum == refined_string_typet::index_of_int(0)) sum = unary_minus_exprt(t);
	else sum = minus_exprt(sum,t);
      else if (second == 1)
	if(sum == refined_string_typet::index_of_int(0)) sum = t;
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

exprt string_refinementt::compute_subst(const exprt &qvar, const exprt &val, const exprt &f) 
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
    debug() << "string_refinementt::compute_subst: qvar not found" << eom;
    debug() << "qvar = " << qvar.pretty() << eom
	    << "val = " << val.pretty() << eom
	    << "f = " << f.pretty() << eom;
    assert(false);
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
	current_index_set[s].insert(bounds.begin(), bounds.end());
	current_index_set[s].insert(i);
	index_set[s].insert(bounds.begin(), bounds.end());
	index_set[s].insert(i);
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
  std::vector<exprt> to_process;
  to_process.push_back(formula);

  while (!to_process.empty()) {
    exprt cur = to_process.back();
    to_process.pop_back();
    if (cur.id() == ID_index) {
      const exprt &s = cur.op0();
      const exprt &i = cur.op1();
      assert(s.type().id() == ID_array);
      const exprt &simplified = simplify_sum(i);
      if(index_set[s].insert(simplified).second)
	current_index_set[s].insert(simplified);
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
  // We are not sure the index set contains only positive numbers
  exprt bounds = and_exprt(axiom.univ_within_bounds(),binary_relation_exprt(zero,ID_le,val));
  replace_expr(axiom.get_univ_var(), r, bounds);
  return string_constraintt(bounds,instance);     
}


void string_refinementt::instantiate_not_contains(const string_constraintt & axiom, std::vector<exprt> & new_lemmas){
  assert(axiom.is_not_contains());
  exprt s0 = axiom.s0();
  exprt s1 = axiom.s1();

  debug() << "instantiate not contains " << pretty_short(s0) << " : " << pretty_short(s1) << eom;
  expr_sett index_set0 = index_set[to_string_expr(s0).content()];
  expr_sett index_set1 = index_set[to_string_expr(s1).content()];

  for(expr_sett::iterator it0 = index_set0.begin(); it0 != index_set0.end(); it0++)
    for(expr_sett::iterator it1 = index_set1.begin(); it1 != index_set1.end(); it1++)
      {
	debug() << pretty_short(*it0) << " : " << pretty_short(*it1) << eom;
	exprt val = minus_exprt(*it0,*it1);
	exprt lemma = implies_exprt(and_exprt(axiom.premise(),equal_exprt(axiom.witness_of(val), *it1)), not_exprt(equal_exprt(to_string_expr(s0)[*it0],to_string_expr(s1)[*it1])));
	new_lemmas.push_back(lemma);
	// we put bounds on the witnesses: 0 <= v <= |s0| - |s1| ==> 0 <= v+w[v] < |s0| && 0 <= w[v] < |s1|
	exprt witness_bounds = implies_exprt
	  (and_exprt(binary_relation_exprt(zero,ID_le,val), binary_relation_exprt(minus_exprt(to_string_expr(s0).length(),to_string_expr(s1).length()),ID_ge,val)),
	   and_exprt(binary_relation_exprt(zero,ID_le,plus_exprt(val,axiom.witness_of(val))),
		     and_exprt(binary_relation_exprt(to_string_expr(s0).length(),ID_gt,plus_exprt(val,axiom.witness_of(val))), 
			       and_exprt(binary_relation_exprt(to_string_expr(s1).length(),ID_gt,axiom.witness_of(val)), 
					 binary_relation_exprt(zero,ID_le,axiom.witness_of(val))))));
	new_lemmas.push_back(witness_bounds);
      }
}

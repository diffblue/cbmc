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

// Succinct version of pretty()
std::string string_refinementt::pretty_short(const exprt & expr) {
  languagest languages(ns, new_ansi_c_language());
  std::string string_value;
  languages.from_expr(expr, string_value);
  return string_value;
}

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

string_axiomt::string_axiomt(symbol_exprt qvar, exprt prem, exprt bod) :
  univ_var(qvar), premise(prem), body(bod), is_quantified(true)
{}

string_axiomt::string_axiomt(symbol_exprt univ, symbol_exprt evar, exprt bound, exprt prem, exprt bod) : string_axiomt(univ,prem,bod)
{ 
  exists_var.push_back(evar);
  exists_bounds.push_back(bound);
}

string_axiomt::string_axiomt(exprt prem, exprt bod)
{
  premise = prem;
  is_quantified = false;
  body = bod;
}

string_axiomt::string_axiomt(exprt bod)
{
  premise = true_exprt();
  is_quantified = false;
  body = bod;
}

string_axiomt::string_axiomt()
{
  premise = false_exprt();
  body = true_exprt();
  is_quantified = false;
}



string_refinementt::string_refinementt(const namespacet &_ns, propt &_prop):
  SUB(_ns, _prop)
{
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
  axioms.emplace_back(qvar,and_exprt(t>qvar,expr.cond()),equal_exprt((*this)[qvar],t[qvar]))
;
  axioms.emplace_back(implies_exprt(not_exprt(expr.cond()),equal_exprt(length(),f.length())));
  symbol_exprt qvar2 = string_refinementt::fresh_symbol("string_if",index_type);
  axioms.emplace_back(qvar2,and_exprt(t>qvar2,expr.cond()),equal_exprt((*this)[qvar],f[qvar]));
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
    axioms.push_back(string_axiomt(lemma));
  }

  std::string s_length_binary = integer2binary(unsigned(sval.size()),INDEX_WIDTH);
  exprt s_length = constant_exprt(s_length_binary, index_type);

  axioms.push_back(string_axiomt(equal_exprt(length(),s_length)));
}


void string_exprt::of_string_concat(const function_application_exprt &f, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); //bad args to string concat
  
  string_exprt s1 = string_exprt::of_expr(args[0],axioms);
  string_exprt s2 = string_exprt::of_expr(args[1],axioms);

  equal_exprt length_sum_lem(length(), plus_exprt(s1.length(), s2.length()));
  axioms.push_back(string_axiomt(length_sum_lem));
  // We can run into problems if the length of the string exceed 32 bits?
  binary_relation_exprt lem1(length(), ID_ge, s1.length());
  axioms.push_back(string_axiomt(lem1));
  binary_relation_exprt lem2(length(), ID_ge, s2.length());
  axioms.push_back(string_axiomt(lem2));

  symbol_exprt idx = string_refinementt::fresh_symbol("index_concat", index_type);

  string_axiomt a1(idx, and_exprt(string_refinementt::is_positive(idx),binary_relation_exprt(idx, ID_lt, s1.length())),
		   equal_exprt(s1[idx],
			       index_exprt(content(), idx)));

  symbol_exprt idx2 = string_refinementt::fresh_symbol("index_concat2", index_type);

  string_axiomt a2(idx2, and_exprt(string_refinementt::is_positive(idx2),binary_relation_exprt(idx2, ID_lt, s2.length())),
		   equal_exprt(s2[idx2],
			       index_exprt(content(), 
					   plus_exprt(idx2,s1.length()))));
  axioms.push_back(a2);
  axioms.push_back(a1);
}

void string_exprt::of_string_substring
(const function_application_exprt &expr, axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); // bad args to string substring?

  string_exprt str = of_expr(args[0],axioms);
  typecast_exprt i(args[1], index_type);
  typecast_exprt j(args[2], index_type);

  symbol_exprt idx = string_refinementt::fresh_symbol("index_substring", index_type);

  // forall idx < str.length, str[idx] = arg_str[idx+i]
  string_axiomt a(idx,
		  binary_relation_exprt(idx, ID_lt, length()),
		  equal_exprt(index_exprt(content(),idx), 
			      str[plus_exprt(i, idx)]));
  axioms.push_back(a);

  and_exprt lemma1(binary_relation_exprt(i, ID_lt, j),
                   and_exprt(binary_relation_exprt(j, ID_le, str.length()),
                             equal_exprt(length(), minus_exprt(j, i))));
  axioms.push_back(string_axiomt(lemma1));

  binary_relation_exprt lemma2(str.length(), ID_ge, length());
  axioms.push_back(string_axiomt(lemma2));
}

void string_exprt::of_string_char_set
(const function_application_exprt &expr,axiom_vect & axioms)
{
  const function_application_exprt::argumentst &args = expr.arguments();  
  assert(args.size() == 3); //bad args to string_char_set?

  string_exprt str = of_expr(args[0],axioms);
  symbol_exprt c = string_refinementt::fresh_symbol("char", char_type);
  
  //THIS HAS NOT BEEN CHECKED:  
  axioms.push_back(equal_exprt(c,args[2]));
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
  for(int i = 0; i < string_axioms.size(); i++)
    if(!string_axioms[i].is_quantified)
      add_implies_lemma(string_axioms[i].premise,string_axioms[i].body);

  add_instantiations(true);

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

void string_refinementt::check_SAT()
{
  SUB::check_SAT();
  if (!progress) {
    if (!check_axioms()) {
      progress = true;
      add_instantiations();
    }
  }
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
}

void string_refinementt::add_implies_lemma(const exprt &prem, const exprt & body)
{
  if (!seen_instances.insert(implies_exprt(prem,body)).second)
    return;

  if(body == true_exprt()) 
    {
      debug() << "add_implies_lemma: tautology" << eom;
      return;
    }
  
  satcheck_no_simplifiert sat_check;
  SUB solver(ns, sat_check);
  solver << prem;

  switch (solver()) {
  case decision_proceduret::D_UNSATISFIABLE:
    debug() << "add_implies_lemma: precondition unsatisfiable" << eom;
    break;
  case decision_proceduret::D_SATISFIABLE: 
  default:
    add_lemma(implies_exprt(prem,body));
  }
}

void string_refinementt::add_lemmas(axiom_vect & lemmas)
{
  axiom_vect::iterator it;
  for(it = lemmas.begin(); it != lemmas.end(); it++)
    {
      // distinguish between lemmas that are not universaly quantified
      if(!(it->is_quantified))
	add_lemma(it->body);
      else 
	string_axioms.push_back(*it);
    }
}




void string_refinementt::make_string(const symbol_exprt & sym, const exprt & str) 
{
  if(str.id()==ID_symbol) {
    symbol_to_string[sym.get_identifier()] = string_exprt::find_symbol(to_symbol_expr(str));
  }
  else {
    axiom_vect lemmas;
    symbol_to_string[sym.get_identifier()] = string_exprt::of_expr(str,lemmas);
    add_lemmas(lemmas);
  }
}

string_exprt string_refinementt::make_string(const exprt & str) 
{
  if(str.id()==ID_symbol) {
    string_exprt s = string_exprt::find_symbol(to_symbol_expr(str));
    return s;
  }
  else {
    axiom_vect lemmas;
    string_exprt s = string_exprt::of_expr(str,lemmas);
    add_lemmas(lemmas);
    return s;
  }
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

  string_axioms.emplace_back(qvar,
			     and_exprt(and_exprt(eq, s1 > qvar),is_positive(qvar)),
			     equal_exprt(s1[qvar],s2[qvar]));

  string_axioms.emplace_back
    (not_exprt(eq),
     or_exprt(notequal_exprt(s1.length(), s2.length()),
	      and_exprt(s1 > witness,
			and_exprt(is_positive(witness),
				  notequal_exprt(s1[witness],s2[witness])))));

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

  symbol_exprt isprefix = fresh_symbol("isprefix");
  boolean_symbols.push_back(isprefix);
  string_exprt s0 = make_string(args[0]);
  string_exprt s1 = make_string(args[1]);
  assert(f.type() == bool_typet());
  bvt bv = convert_bv(isprefix); 

  add_lemma(implies_exprt(isprefix, s1 >= s0));

  symbol_exprt qvar = fresh_symbol("qvar_prefix", index_type);
  string_axioms.emplace_back(qvar, and_exprt(isprefix, s0 > qvar),
			     equal_exprt(s0[qvar],s1[qvar]));
	     
  symbol_exprt witness = fresh_symbol("index_prefix", index_type);
  index_symbols.push_back(witness);

  // forall witness < s0.length. isprefix => s0[witness] = s2[witness]

  or_exprt s0_notpref_s1(not_exprt(s1 >= s0),
			 and_exprt(s0 > witness, 
				   
				   notequal_exprt(s0[witness],s1[witness])));
		       
  add_lemma(implies_exprt (not_exprt(isprefix),and_exprt(is_positive(witness),s0_notpref_s1)));
  return bv;
}


bvt string_refinementt::convert_string_is_suffix(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string issuffix?

  symbol_exprt issuffix = fresh_symbol("issuffix");
  boolean_symbols.push_back(issuffix);

  string_exprt s0 = make_string(args[0]);
  string_exprt s1 = make_string(args[1]);


  // issufix(s1,s0) => s0.length >= s1.length
  // && forall witness < s1.length. 
  //     issufix => s1[witness] = s0[witness + s0.length - s1.length]
  // && !issuffix => s1.length > s0.length 
  //       || (s1.length > witness && s1[witness] != s0[witness + s0.length - s1.length]

  add_lemma(implies_exprt(issuffix, s1 >= s0));

  symbol_exprt qvar = fresh_symbol("qvar_suffix", index_type);
  exprt qvar_shifted = plus_exprt(qvar, 
				  minus_exprt(s1.length(), s0.length()));
  string_axioms.emplace_back(qvar, and_exprt(issuffix, s0 > qvar),
			     equal_exprt(s0[qvar],s1[qvar_shifted]));

  symbol_exprt witness = fresh_index("witness_not_suffix");

  exprt shifted = plus_exprt(witness, 
			     minus_exprt(s1.length(), s0.length()));

  implies_exprt lemma2(not_exprt(issuffix),
		       and_exprt(is_positive(witness),
				 or_exprt(s0 > s1,
					  and_exprt(s0 > witness, 
						    notequal_exprt(s0[witness],s1[shifted])))));

  add_lemma(lemma2);

  assert(f.type() == bool_typet());
  bvt bv = convert_bv(issuffix);

  return bv;
}


bvt string_refinementt::convert_string_contains(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string contains?

  symbol_exprt contains = fresh_symbol("contains");
  boolean_symbols.push_back(contains);

  string_exprt s0 = make_string(args[0]);
  string_exprt s1 = make_string(args[1]);

  // contains => s0.length >= s1.length
  // && startpos <= s0.length - s1.length
  // && forall qvar < s1.length.
  //     contains => s1[qvar] = s0[startpos + qvar]
  // !contains => s1.length > s0.length 
  //       || (forall startpos <= s0.length - s1.length. 
  //             exists witness < s1.length && s1[witness] != s0[witness + startpos]

  add_lemma(implies_exprt(contains, s0 >= s1));

  symbol_exprt startpos = fresh_symbol("startpos", index_type);
  index_symbols.push_back(startpos);

  add_lemma(implies_exprt(contains,and_exprt(is_positive(startpos),binary_relation_exprt(startpos, ID_le, minus_exprt(s0.length(),s1.length())))));

  symbol_exprt qvar = fresh_symbol("qvar", index_type);
  exprt qvar_shifted = plus_exprt(qvar, startpos);
  string_axioms.emplace_back(qvar, and_exprt(contains, s1 > qvar),
			     equal_exprt(s1[qvar],s0[qvar_shifted]));

  // We rewrite the axiom for !contains as:
  // forall startpos. exists witness. (!contains && |s0| >= |s1| && stratpos <= |s0| - |s1|)
  //      ==> witness < |s1| && s1[witness] != s0[startpos+witness]

  symbol_exprt qstartpos = fresh_symbol("qstartpos", index_type);
  symbol_exprt witness = fresh_symbol("witness", index_type);
  exprt shifted = plus_exprt(witness, qstartpos);
  add_lemma(is_positive(witness));

  string_axioms.emplace_back
    (qstartpos,witness,s1.length(),
     and_exprt(not_exprt(contains),
	       and_exprt(s0 >= s1,
			 binary_relation_exprt
			 (qstartpos,ID_le,
			  minus_exprt(s0.length(),s1.length())))),
     notequal_exprt(s1[witness],s0[shifted]));


  assert(f.type() == bool_typet());
  bvt bv = convert_bv(contains);

  return bv;
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
  assert(args.size() == 2); // bad args to string contains?

  symbol_exprt index = fresh_index("index_of");
  string_exprt str = make_string(args[0]);
  exprt c = args[1];
  assert(is_unrefined_char_type(c.type()));
  // (i = -1 || 0 <= i < s && s[i] = c) && forall n. n < i => s[n] != c 
  
  string_axioms.push_back((string_axiomt(str > index) && is_positive(index)) || equal_exprt(index,index_of_int(-1)));

  symbol_exprt n = fresh_symbol("qvar",index_type);

  string_axioms.push_back((! string_axiomt::equality(str[n],c))
			  .forall(n,index));
			  

  bvt bv = convert_bv(index);
  return bv;
}

bvt string_refinementt::convert_string_last_index_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  assert(args.size() == 2); // bad args to string contains?

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
  index_set[str.content()].insert(args[1]);
  return convert_bv(str[args[1]]);
}



////////////////////
// PASS Algorithm //
////////////////////

// We compute the index set for all formulas, instantiate the formulas
// with the found indexes, and add them as lemmas.
void string_refinementt::add_instantiations(bool first)
{
  //debug() << "string_refinementt::add_instantiations" << eom;
  if (first) {
    for (size_t i = 0; i < string_axioms.size(); ++i) {
      update_index_set(string_axioms[i]);
    }
  }
  for (size_t i = 0; i < cur.size(); ++i) {
    update_index_set(cur[i]);
  }

  cur.clear();

  debug() << "string_refinementt::add_instantiations: "
	  << "going through the index set:" << eom;
  for (std::map<exprt, expr_sett>::iterator i = index_set.begin(),
	 end = index_set.end(); i != end; ++i) {
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
        string_axiomt lemma = instantiate(string_axioms[k], s, val);
	assert(!lemma.is_quantified);
	add_implies_lemma(lemma.premise,lemma.body);
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
      debug() << it->first << " = " << pretty_short(it->second) << " of length " << pretty_short(len) <<" := " << string_of_array(econtent,len) << eom;
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

  std::vector< std::pair<size_t, exprt> > violated;

  debug() << "there are " << string_axioms.size() << " string axioms" << eom;
  for (size_t i = 0; i < string_axioms.size(); ++i) {
    const string_axiomt &axiom = string_axioms[i];

    exprt negaxiom = and_exprt(axiom.premise, not_exprt(axiom.body));
    replace_expr(fmodel, negaxiom);

    satcheck_no_simplifiert sat_check;
    SUB solver(ns, sat_check);
    solver << negaxiom;

    switch (solver()) {
    case decision_proceduret::D_SATISFIABLE: {
      //debug() << "satisfiable" << eom;
      exprt val = solver.get(axiom.univ_var);
      violated.push_back(std::make_pair(i, val));
    } break;
    case decision_proceduret::D_UNSATISFIABLE:
      //debug() << "unsatisfiable" << eom;
      break;
    default:
      throw "failure in checking axiom";
      //expect(false, "failure in checking axiom");
    }
  }

  if (violated.empty()) {
    debug() << "no violated property" << eom;
    return true;
  }

  bool all_seen = true;
  
  debug() << violated.size() << " string axioms can be violated" << eom;

  for (size_t i = 0; i < violated.size(); ++i) {
    const exprt &val = violated[i].second;
    const string_axiomt &axiom = string_axioms[violated[i].first];
    exprt premise(axiom.premise);
    exprt body(axiom.body);
    implies_exprt instance(premise, body);
    replace_expr(axiom.univ_var, val, instance);
    if (seen_instances.insert(instance).second) {
      add_implies_lemma(premise,body);
      all_seen = false;
    } else debug() << "instance already seen" << eom;
    // TODO - add backwards instantiations
  }
  
  return all_seen;
  //return false;
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


exprt string_refinementt::compute_subst(const exprt &qvar, const exprt &val, const exprt &f, exprt & positive, exprt & negative)
{

  //std::cout << "compute_subst (" << pretty_short(qvar) << "," << val << "," << f << ")" << std::endl;
  std::vector< std::pair<exprt, bool> > to_process;

  // number of time the element should be added (can be negative)
  std::map< exprt, int> elems;
  // qvar has to be equal to val - f(0) if it appears positively in f 
  // (ie if f(qvar) = f(0) + qvar) and f(0) - val if it appears negatively 
  // in f. So we start by computing val - f(0).
  to_process.push_back(std::make_pair(val,true));
  to_process.push_back(std::make_pair(f, false));

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

  bool found = false;
  bool neg = false; // true if qvar appears negatively in f, ie positively in the elements

  negative = index_of_int(0);
  positive = index_of_int(0);  


  for (std::map<exprt,int>::iterator it = elems.begin();
       it != elems.end(); it++) {
    const exprt &t = it->first;
    if (t == qvar) {
      if(it->second == 1 || it->second == -1){
	found = true;
	neg = (it->second == 1);
      } else 
	debug() << "in string_refinementt::compute_subst:"
		<< " warning: occurences of qvar canceled out " << eom;
    } else 
      if (it->second != 0)
	if (it->second == -1) 
	  if(negative == index_of_int(0)) negative = t;
	  else negative = plus_exprt(negative,t);
	else if (it->second == 1)
	  if(positive == index_of_int(0)) positive = t;
	  else positive = plus_exprt(positive, t);
	else assert(false);
  }
  
  
  if (!found) { 
    // we should add a lemma to say that val == f
    debug() << "not sure we need to add a lemma: to say val == f" << eom;
    add_lemma(equal_exprt(val,f));
    return qvar;
  }

  if (neg) positive.swap(negative);
  
  if(negative == index_of_int(0)) 
    return positive;  
  else 
    if(positive == index_of_int(0)) 
      {
	debug() << "return unary_minus_exprt: this probably shouldn't happen" << eom;
	return unary_minus_exprt(negative);
      }
    else 
      return minus_exprt(positive,negative);
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


void string_refinementt::update_index_set(const string_axiomt &axiom)
{
  std::vector<exprt> bounds;
  get_bounds(axiom.univ_var, axiom.premise, bounds);

  std::vector<exprt> to_process;
  to_process.push_back(axiom.body);
  while (!to_process.empty()) {
    exprt cur = to_process.back();
    to_process.pop_back();
    if (cur.id() == ID_index) {
      const exprt &s = cur.op0();
      const exprt &i = cur.op1();

      // if cur is of the form s[i] and qvar does not appear in i...
      if(!find_qvar(i,axiom.univ_var)) {
	assert(s.type() == string_type.get_content_type());
	expr_sett &idxs = index_set[s];
        idxs.insert(bounds.begin(), bounds.end());
        idxs.insert(i);
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
      assert(s.type() == string_type.get_content_type());
      index_set[s].insert(i);
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



string_axiomt string_refinementt::instantiate(const string_axiomt &axiom,
                                      const exprt &str, const exprt &val)
{
  exprt idx = find_index(axiom.body,str);
  // what if idx is qvar or if there are several indexes?
  if(idx.is_nil()) return string_axiomt();
  if(!find_qvar(idx,axiom.univ_var)) return string_axiomt(); 

  exprt positive;
  exprt negative;
  exprt r = compute_subst(axiom.univ_var, val, idx,positive,negative);
  exprt premise(axiom.premise);
  exprt body(axiom.body);

  /*debug() << "string_refinementt::instantiate : replaces " << eom 
	  << "occurances of " << pretty_short(axiom.univ_var) << eom
	  << "by " << pretty_short(r)  << eom 
	  << "in " << pretty_short(instance) << eom;*/

  replace_expr(axiom.univ_var, r, premise);
  replace_expr(axiom.univ_var, r, body);
  replace_expr(axiom.univ_var, r, positive);
  replace_expr(axiom.univ_var, r, negative);


  for(unsigned i=0; i < axiom.exists_var.size(); i++) {
    debug() << "string_refinementt::instantiate : generate a fresh variable for existentially quantified variables, assume it has to be positive" << eom;
    symbol_exprt fresh_var = fresh_symbol("exists_remove", index_type);
    index_symbols.push_back(fresh_var);
    add_lemma(is_positive(fresh_var));
    add_lemma(binary_relation_exprt(fresh_var,ID_lt,axiom.exists_bounds[i]));
    /*if(find_qvar(premise,axiom.exists_var[i])){
      debug() << "warning: existential variable appearing on the premise of axiom : "
	      << axiom_to_string(axiom) << eom
	      << "we should probably disregard this lemma." << eom;
      debug() << " r = " << pretty_short(r) << eom;
      debug() << " str = " << pretty_short(str) << eom;
      debug() << " val = " << pretty_short(val) << eom;
      }*/
    replace_expr(axiom.exists_var[i],fresh_var,body);
    replace_expr(axiom.exists_var[i],fresh_var,positive);
    replace_expr(axiom.exists_var[i],fresh_var,negative);
    replace_expr(axiom.exists_var[i],fresh_var,premise);
 
  }


  //debug() << "Warning: adding condition saying that " << axiom.univ_var.get_identifier() << " is positive" << eom;     //return string_axiomt(and_exprt(binary_relation_exprt(positive,ID_ge,negative),premise),body); 
  return string_axiomt(premise,body); 
}


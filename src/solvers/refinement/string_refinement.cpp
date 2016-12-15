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
#include <langapi/language_util.h>

string_refinementt::string_refinementt(const namespacet &_ns, propt &_prop):
  SUB(_ns, _prop)
{
  use_counter_example = false;
  //use_counter_example = true;
  variable_with_multiple_occurence_in_index = false;
  initial_loop_bound = 100;
  start_time = std::chrono::high_resolution_clock::now();
}

void string_refinementt::set_mode()
{
  debug() << "initializing mode" << eom;
  // symbol_table.show(std::cout);
  symbolt init = ns.lookup(irep_idt("__CPROVER_initialize"));
  irep_idt mode = init.mode;
  debug() << "mode detected as " << mode << eom;
  generator.set_mode(mode);
}

void string_refinementt::display_index_set() {
  for (std::map<exprt, expr_sett>::iterator i = index_set.begin(),
	 end = index_set.end(); i != end; ++i) {
    const exprt &s = i->first;
    debug() << "IS(" << from_expr(s) << ") == {";

    for (expr_sett::const_iterator j = i->second.begin(), end = i->second.end();
         j != end; ++j)
      debug() << from_expr(*j) << "; ";
    debug() << "}"  << eom;
  }
}

// We compute the index set for all formulas, instantiate the formulas
// with the found indexes, and add them as lemmas.
void string_refinementt::add_instantiations()
{
  debug() << "string_constraint_generatort::add_instantiations: "
	  << "going through the current index set:" << eom;
  for (std::map<exprt, expr_sett>::iterator i = current_index_set.begin(),
	 end = current_index_set.end(); i != end; ++i) {
    const exprt &s = i->first;
    debug() << "IS(" << from_expr(s) << ") == {";

    for (expr_sett::const_iterator j = i->second.begin(), end = i->second.end();
         j != end; ++j)
      debug() << from_expr(*j) << "; ";
    debug() << "}"  << eom;


    for (expr_sett::const_iterator j = i->second.begin(), end = i->second.end();
         j != end; ++j) {
      const exprt &val = *j;

      for (size_t k = 0; k < universal_axioms.size(); ++k) {
	assert(universal_axioms[k].is_univ_quant());
	exprt lemma = instantiate(universal_axioms[k], s, val);
	add_lemma(lemma);
      }
    }
  }
}

literalt string_refinementt::convert_rest(const exprt &expr)
{
  if(expr.id()==ID_function_application)
    {
      // can occur in __CPROVER_assume
      bvt bv = convert_function_application(to_function_application_expr(expr));
      assert(bv.size() == 1);
      return bv[0];
    }
  else
    {
      return SUB::convert_rest(expr);
    }
}

bvt string_refinementt::convert_symbol(const exprt &expr)
{
  const typet &type = expr.type();
  const irep_idt &identifier = expr.get(ID_identifier);
  assert(!identifier.empty());

  if (refined_string_typet::is_unrefined_string_type(type))
    {
      string_exprt str = generator.find_or_add_string_of_symbol(to_symbol_expr(expr));
      bvt bv = convert_bv(str);
      return bv;
    }
  else return SUB::convert_symbol(expr);
}


bvt string_refinementt::convert_function_application(const function_application_exprt &expr)
{
  debug() << "string_refinementt::convert_function_application "  << from_expr(expr) << eom;
  exprt f = generator.add_axioms_for_function_application(expr);
  return convert_bv(f);
}

bool string_refinementt::boolbv_set_equality_to_true(const equal_exprt &expr)
{
  if(!equality_propagation) return true;

  // We should not do that everytime, but I cannot find
  // another good entry point
  if(generator.get_mode() == ID_unknown)
    set_mode();

  const typet &type=ns.follow(expr.lhs().type());

  if(expr.lhs().id()==ID_symbol &&
     // We can have affectation of string from StringBuilder or CharSequence
     //type==ns.follow(expr.rhs().type()) &&
     type.id()!=ID_bool)
  {
    debug() << "string_refinementt " << from_expr(expr.lhs()) << " <- "
	    << from_expr(expr.rhs()) << eom;

    if(refined_string_typet::is_unrefined_string_type(type))
      {
	symbol_exprt sym = to_symbol_expr(expr.lhs());
	generator.set_string_symbol_equal_to_expr(sym,expr.rhs());
	return false;
      }
    else if(type==ns.follow(expr.rhs().type()))
      {
	if(is_unbounded_array(type)) return true;
	const bvt &bv1=convert_bv(expr.rhs());
	const irep_idt &identifier=
	  to_symbol_expr(expr.lhs()).get_identifier();
	map.set_literals(identifier, type, bv1);
	if(freeze_all) set_frozen(bv1);
	return false;
      }
  }

  return true;
}



void string_refinementt::print_time(std::string s)
{
  debug() << s << " TIME == "
	  << (std::chrono::duration_cast<std::chrono::microseconds>
	      (std::chrono::high_resolution_clock::now()-start_time).count()  / 1000)
	  << eom;
}

decision_proceduret::resultt string_refinementt::dec_solve()
{
  print_time("string_refinementt::dec_solve");
  for(unsigned i = 0; i < generator.axioms.size(); i++)
    if(generator.axioms[i].id() == ID_string_constraint)
    {
      debug() << "universaly quantified " << eom;
      // << generator.axioms[i].pretty() << eom;
      string_constraintt c= to_string_constraint(generator.axioms[i]);
      universal_axioms.push_back(c);
    }
    else if(generator.axioms[i].id() == ID_string_not_contains_constraint)
    {
      string_not_contains_constraintt axiom=
	to_string_not_contains_constraint(generator.axioms[i]);
      generator.witness[axiom] = string_exprt::fresh_symbol
	("not_contains_witness",
	 array_typet(refined_string_typet::index_type(),
		     infinity_exprt(refined_string_typet::index_type())));
      not_contains_axioms.push_back(axiom);
    }
    else
      add_lemma(generator.axioms[i]);

  initial_index_set(universal_axioms);
  debug() << "string_refinementt::dec_solve: warning update_index_set has to be checked" << eom;
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
	    {
	      debug() << "WARNING: some variable appears multiple times" << eom;
	    }

	  if(current_index_set.empty()){
	    debug() << "current index set is empty" << eom;
	    return D_SATISFIABLE;
	  }

	  display_index_set();
	  debug()<< "instantiating NOT_CONTAINS constraints" << eom;
	  for(unsigned i=0; i<not_contains_axioms.size(); i++) {
	    debug()<< "constraint " << i << eom;
	    std::vector<exprt> lemmas;
	    instantiate_not_contains(not_contains_axioms[i],lemmas);
	    for(unsigned j=0; j<lemmas.size(); j++) {
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

void string_refinementt::add_lemma(const exprt &lemma, bool add_to_index_set)
{
  if (!seen_instances.insert(lemma).second)
    {
      debug() << "string_refinementt::add_lemma : already seen" << eom;
      return;
    }

  if(lemma == true_exprt())
    {
      debug() << "string_refinementt::add_lemma : tautology" << eom;
      return;
    }

  debug() << "adding lemma " << from_expr(lemma) << eom;

  prop.l_set_to_true(convert(lemma));
  if(add_to_index_set)
    cur.push_back(lemma);
}

int integer_of_expr(const constant_exprt & expr)
{
  mp_integer i;
  assert(!to_integer(expr,i));
  if(i<0)
    return -integer2unsigned(-i);
  else
    return integer2unsigned(i);
}

std::string string_refinementt::string_of_array(const exprt &arr, const exprt &size)
{
  if(size.id() != ID_constant) return "string of unknown size";
  int n = integer_of_expr(to_constant_expr(size));
  if(n<0) return "string of wrong size";
  if(n>500) return "very long string";
  if(n==0) return "\"\"";
  unsigned str[n];
  exprt val = get(arr);
  if(val.id() == "array-list") {
    for (size_t i = 0; i < val.operands().size()/2; i++) {
      exprt index = val.operands()[i*2];
      int idx = integer_of_expr(to_constant_expr(index));
      if(idx<n)
      {
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
  if(arr.type().subtype() == generator.get_char_type())
    chart = generator.get_char_type();
  else {
    assert(false);
    //assert(arr.type().subtype() == java_char_type);
    //chart = java_char_type;
  }

  if(val.id() == "array-list") {
    exprt ret =
      array_of_exprt(chart.zero_expr(), array_typet(chart, infinity_exprt(generator.get_index_type())));

    for (size_t i = 0; i < val.operands().size()/2; i++) {
      exprt index = val.operands()[i*2];
      assert(index.type() == generator.get_index_type());
      exprt value = val.operands()[i*2+1];
      //assert(value.type() == char_type || value.type() == java_char_type);
      assert(value.type() == generator.get_char_type());
      ret = with_exprt(ret, index, value);
    }
    return ret;

  } else {
    debug() << "unable to get array-list value of "
	    << from_expr(val) << eom;
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
  for (it = generator.symbol_to_string.begin(); it != generator.symbol_to_string.end(); ++it)
    {
      string_exprt refined = it->second;
      const exprt &econtent = refined.content();
      const exprt &elength  = refined.length();

      exprt len = get(elength);
      exprt arr = get_array(econtent, len);

      fmodel[elength] = len;
      fmodel[econtent] = arr;
      debug() << it->first << " = " << from_expr(it->second)
	      << " of length " << from_expr(len) <<" := " << eom
	      << from_expr(get(econtent)) << eom
	      << string_of_array(econtent,len) << eom;
    }

  for(std::vector<symbol_exprt>::iterator it = generator.boolean_symbols.begin();
      it != generator.boolean_symbols.end(); it++) {
    debug() << "" << it->get_identifier() << " := " << from_expr(get(*it)) << eom;
    fmodel[*it] = get(*it);
  }

  for(std::vector<symbol_exprt>::iterator it = generator.index_symbols.begin();
      it != generator.index_symbols.end(); it++) {
    debug() << "" << it->get_identifier() << " := " << from_expr(get(*it)) << eom;
    fmodel[*it] = get(*it);
  }

  debug() << "in check axiom, the model may be incomplete" << eom;
  std::vector< std::pair<size_t, exprt> > violated;

  debug() << "there are " << universal_axioms.size() << " universal axioms" << eom;
  for (size_t i = 0; i < universal_axioms.size(); ++i) {
    const string_constraintt &axiom = universal_axioms[i];

    exprt negaxiom = and_exprt(axiom.premise(), not_exprt(axiom.body()));
    replace_expr(fmodel, negaxiom);

    debug() << "negaxiom: " << from_expr(negaxiom) << eom;

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
    exprt val = get(generator.get_witness_of(not_contains_axioms[i],refined_string_typet::index_zero()));
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
  exprt sum = refined_string_typet::index_of_int(0);
  mp_integer constants = 0;

  for (std::map<exprt,int>::iterator it = m.begin();
       it != m.end(); it++) {
    // We should group constants together...
    const exprt &t = it->first;
    int second = negated?(-it->second):it->second;
    if(t.id() == ID_constant)
      {
	std::string value(to_constant_expr(t).get_value().c_str());
	constants += binary2integer(value,true) * second;
      }
    else
      {
	if(second != 0)
	  {
	    if(second == -1)
	      {
		if(sum == refined_string_typet::index_of_int(0)) sum = unary_minus_exprt(t);
		else sum = minus_exprt(sum,t);
	      }
	    else if(second == 1)
	      {
		if(sum == refined_string_typet::index_of_int(0)) sum = t;
		else sum = plus_exprt(sum, t);
	      }
	  }
	else
	  {
	    debug() << "in string_refinementt::sum_of_map:"
		    << " warning: several occurences of the same variable: "
		    << t.pretty() << eom;
	    variable_with_multiple_occurence_in_index = true;
	    if(second > 1)
	      for(int i = 0; i < second; i++)
		sum = plus_exprt(sum, t);
	    else
	      for(int i = 0; i > second; i--)
		sum = minus_exprt(sum, t);
	  }
      }
  }

  return plus_exprt(sum,constant_exprt(integer2binary(constants, STRING_SOLVER_INDEX_WIDTH), refined_string_typet::index_type()));
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
static bool find_qvar(const exprt index, const symbol_exprt & qvar)
{
  find_qvar_visitor v2(qvar);
  try {
    index.visit(v2);
    return false;
  } catch (bool found) {return found;}
}


void string_refinementt::initial_index_set
(const std::vector<string_constraintt>  & string_axioms)
{
  for (size_t i = 0; i < string_axioms.size(); ++i)
    initial_index_set(string_axioms[i]);
}

void string_refinementt::update_index_set(const std::vector<exprt> & cur) {
  for (size_t i = 0; i < cur.size(); ++i) {
    update_index_set(cur[i]);
  }
}

void string_refinementt::initial_index_set(const string_constraintt &axiom)
{
  assert(axiom.is_univ_quant());
  symbol_exprt qvar = axiom.get_univ_var();
  std::vector<exprt> to_process;
  to_process.push_back(axiom.body());

  while (!to_process.empty())
    {
      exprt cur = to_process.back();
      to_process.pop_back();
      if (cur.id() == ID_index)
	{
	  const exprt &s = cur.op0();
	  const exprt &i = cur.op1();

	  bool has_quant_var = find_qvar(i,qvar);

	  // if cur is of the form s[i] and no quantified variable appears in i
	  if(!has_quant_var)
	    {
	      current_index_set[s].insert(i);
	      index_set[s].insert(i);
	    }
	  else
	    {
	      // otherwise we add k-1
	      exprt e(i);
	      replace_expr(qvar,
			   minus_exprt(axiom.upper_bound(),
				       refined_string_typet::index_of_int(1)),e);
	      current_index_set[s].insert(e);
	      index_set[s].insert(e);
	    }

	}
      else
	forall_operands(it, cur)
	  to_process.push_back(*it);
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
      if(index_set[s].insert(simplified).second) {
	debug() << "adding to index set of " << from_expr(s)
		<< ": " << from_expr(simplified) << eom;
	current_index_set[s].insert(simplified);
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



exprt string_refinementt::instantiate(const string_constraintt &axiom,
				     const exprt &str, const exprt &val)
{
  assert(axiom.is_univ_quant());
  exprt idx = find_index(axiom.body(),str);
  if(idx.is_nil()) return true_exprt();
  if(!find_qvar(idx,axiom.get_univ_var())) return true_exprt();

  exprt r = compute_subst(axiom.get_univ_var(), val, idx);
  implies_exprt instance(axiom.premise(), axiom.body());
  replace_expr(axiom.get_univ_var(), r, instance);
  // We are not sure the index set contains only positive numbers
  exprt bounds = and_exprt(axiom.univ_within_bounds(),binary_relation_exprt(refined_string_typet::index_zero(),ID_le,val));
  replace_expr(axiom.get_univ_var(), r, bounds);
  return implies_exprt(bounds,instance);
}


void string_refinementt::instantiate_not_contains(const string_not_contains_constraintt & axiom, std::vector<exprt> & new_lemmas)
{
  exprt s0 = axiom.s0();
  exprt s1 = axiom.s1();

  debug() << "instantiate not contains " << from_expr(s0) << " : " << from_expr(s1) << eom;
  expr_sett index_set0 = index_set[to_string_expr(s0).content()];
  expr_sett index_set1 = index_set[to_string_expr(s1).content()];

  for(expr_sett::iterator it0 = index_set0.begin(); it0 != index_set0.end(); it0++)
    for(expr_sett::iterator it1 = index_set1.begin(); it1 != index_set1.end(); it1++)
      {
	debug() << from_expr(*it0) << " : " << from_expr(*it1) << eom;
	exprt val = minus_exprt(*it0, *it1);
	exprt witness = generator.get_witness_of(axiom,val);
	and_exprt prem_and_is_witness(axiom.premise(),
				      equal_exprt(witness, *it1));

	not_exprt differ(equal_exprt(to_string_expr(s0)[*it0],
				     to_string_expr(s1)[*it1]));
	exprt lemma = implies_exprt(prem_and_is_witness,differ);
				    
	new_lemmas.push_back(lemma);
	// we put bounds on the witnesses: 0 <= v <= |s0| - |s1| ==> 0 <= v+w[v] < |s0| && 0 <= w[v] < |s1|
	exprt witness_bounds = implies_exprt
	  (and_exprt(binary_relation_exprt(refined_string_typet::index_zero(),ID_le,val), binary_relation_exprt(minus_exprt(to_string_expr(s0).length(),to_string_expr(s1).length()),ID_ge,val)),
	   and_exprt(binary_relation_exprt(refined_string_typet::index_zero(),ID_le,plus_exprt(val,witness)),
		     and_exprt(binary_relation_exprt(to_string_expr(s0).length(),ID_gt,plus_exprt(val,witness)),
			       and_exprt(binary_relation_exprt(to_string_expr(s1).length(),ID_gt,witness),
					 binary_relation_exprt(refined_string_typet::index_zero(),ID_le,witness)))));
	new_lemmas.push_back(witness_bounds);
      }
}

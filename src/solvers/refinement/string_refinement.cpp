/*******************************************************************\

Module: String support via creating string constraints and progressively
        instantiating the universal constraints as needed.
        The procedure is described in the PASS paper at HVC'13:
        "PASS: String Solving with Parameterized Array and Interval Automaton"
        by Guodong Li and Indradeep Ghosh.

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

/// \file
/// String support via creating string constraints and progressively
///   instantiating the universal constraints as needed. The procedure is
///   described in the PASS paper at HVC'13: "PASS: String Solving with
///   Parameterized Array and Interval Automaton" by Guodong Li and Indradeep
///   Ghosh.

#include <solvers/refinement/string_refinement.h>

#include <sstream>
#include <ansi-c/string_constant.h>
#include <util/cprover_prefix.h>
#include <util/replace_expr.h>
#include <solvers/sat/satcheck.h>
#include <langapi/language_util.h>

string_refinementt::string_refinementt(
  const namespacet &_ns, propt &_prop, unsigned refinement_bound):
  supert(_ns, _prop),
  use_counter_example(false),
  initial_loop_bound(refinement_bound)
{ }

/// determine which language should be used
void string_refinementt::set_mode()
{
  debug() << "initializing mode" << eom;
  symbolt init=ns.lookup(irep_idt(CPROVER_PREFIX"initialize"));
  irep_idt mode=init.mode;
  debug() << "mode detected as " << mode << eom;
  generator.set_mode(mode);
}

/// display the current index set, for debugging
void string_refinementt::display_index_set()
{
  for(const auto &i : index_set)
  {
    const exprt &s=i.first;
    debug() << "IS(" << from_expr(s) << ")=={";

    for(auto j : i.second)
      debug() << from_expr(j) << "; ";
    debug() << "}"  << eom;
  }
}

/// compute the index set for all formulas, instantiate the formulas with the
/// found indexes, and add them as lemmas.
void string_refinementt::add_instantiations()
{
  debug() << "string_constraint_generatort::add_instantiations: "
          << "going through the current index set:" << eom;
  for(const auto &i : current_index_set)
  {
    const exprt &s=i.first;
    debug() << "IS(" << from_expr(s) << ")=={";

    for(const auto &j : i.second)
      debug() << from_expr(j) << "; ";
    debug() << "}"  << eom;

    for(const auto &j : i.second)
    {
      const exprt &val=j;

      for(const auto &ua : universal_axioms)
      {
        exprt lemma=instantiate(ua, s, val);
        add_lemma(lemma);
      }
    }
  }
}

/// if the expression is a function application, we convert it using our own
/// convert_function_application method
/// \par parameters: an expression
/// \return a literal
literalt string_refinementt::convert_rest(const exprt &expr)
{
  if(expr.id()==ID_function_application)
  {
    // can occur in __CPROVER_assume
    bvt bv=convert_function_application(to_function_application_expr(expr));
    assert(bv.size()==1);
    return bv[0];
  }
  else
  {
    return supert::convert_rest(expr);
  }
}

/// if the expression as string type, look up for the string in the list of
/// string symbols that we maintain, and convert it; otherwise use the method of
/// the parent class
/// \par parameters: an expression
/// \return a bitvector
bvt string_refinementt::convert_symbol(const exprt &expr)
{
  const typet &type=expr.type();
  const irep_idt &identifier=expr.get(ID_identifier);
  assert(!identifier.empty());

  if(refined_string_typet::is_refined_string_type(type))
  {
    string_exprt str=
      generator.find_or_add_string_of_symbol(to_symbol_expr(expr));
    bvt bv=convert_bv(str);
    return bv;
  }
  else
    return supert::convert_symbol(expr);
}

/// generate an expression, add lemmas stating that this expression corresponds
/// to the result of the given function call, and convert this expression
/// \par parameters: a function_application
/// \return a bitvector
bvt string_refinementt::convert_function_application
(const function_application_exprt &expr)
{
  debug() << "string_refinementt::convert_function_application "
          << from_expr(expr) << eom;
  exprt f=generator.add_axioms_for_function_application(expr);
  return convert_bv(f);
}

/// add lemmas to the solver corresponding to the given equation
/// \par parameters: an equality expression
/// \return a Boolean flag to signal a proble
bool string_refinementt::boolbv_set_equality_to_true(const equal_exprt &expr)
{
  if(!equality_propagation)
    return true;

  // We should not do that everytime, but I cannot find
  // another good entry point
  if(generator.get_mode()==ID_unknown)
    set_mode();

  typet type=ns.follow(expr.lhs().type());

  if(expr.lhs().id()==ID_symbol &&
     // We can have affectation of string from StringBuilder or CharSequence
     // type==ns.follow(expr.rhs().type()) &&
     type.id()!=ID_bool)
  {
    debug() << "string_refinementt " << from_expr(expr.lhs()) << " <- "
            << from_expr(expr.rhs()) << eom;


    if(expr.rhs().id()==ID_typecast)
    {
      exprt uncast=to_typecast_expr(expr.rhs()).op();
      if(refined_string_typet::is_refined_string_type(uncast.type()))
      {
        debug() << "(sr) detected casted string" << eom;
        symbol_exprt sym=to_symbol_expr(expr.lhs());
        generator.set_string_symbol_equal_to_expr(sym, uncast);
        return false;
      }
    }

    if(refined_string_typet::is_refined_string_type(type))
    {
      symbol_exprt sym=to_symbol_expr(expr.lhs());
      generator.set_string_symbol_equal_to_expr(sym, expr.rhs());
      return false;
    }
    else if(type==ns.follow(expr.rhs().type()))
    {
      if(is_unbounded_array(type))
        return true;
      bvt bv1=convert_bv(expr.rhs());
      const irep_idt &identifier=
        to_symbol_expr(expr.lhs()).get_identifier();
      map.set_literals(identifier, type, bv1);
      if(freeze_all)
        set_frozen(bv1);
      return false;
    }
  }

  return true;
}

/// use a refinement loop to instantiate universal axioms, call the sat solver,
/// and instantiate more indexes if needed.
/// \return result of the decision procedure
decision_proceduret::resultt string_refinementt::dec_solve()
{
  for(const exprt &axiom : generator.axioms)
    if(axiom.id()==ID_string_constraint)
    {
      string_constraintt c=to_string_constraint(axiom);
      universal_axioms.push_back(c);
    }
    else if(axiom.id()==ID_string_not_contains_constraint)
    {
      string_not_contains_constraintt nc_axiom=
        to_string_not_contains_constraint(axiom);
      refined_string_typet rtype=to_refined_string_type(nc_axiom.s0().type());
      const typet &index_type=rtype.get_index_type();
      array_typet witness_type(index_type, infinity_exprt(index_type));
      generator.witness[nc_axiom]=
        generator.fresh_symbol("not_contains_witness", witness_type);
      not_contains_axioms.push_back(nc_axiom);
    }
    else
    {
      add_lemma(axiom);
    }

  initial_index_set(universal_axioms);
  update_index_set(cur);
  cur.clear();
  add_instantiations();

  while((initial_loop_bound--)>0)
  {
    decision_proceduret::resultt res=supert::dec_solve();

    switch(res)
    {
    case D_SATISFIABLE:
      if(!check_axioms())
      {
        debug() << "check_SAT: got SAT but the model is not correct" << eom;
      }
      else
      {
        debug() << "check_SAT: the model is correct" << eom;
        return D_SATISFIABLE;
      }

      debug() <<  "refining..." << eom;
      // Since the model is not correct although we got SAT, we need to refine
      // the property we are checking by adding more indices to the index set,
      // and instantiating universal formulas with this indices.
      // We will then relaunch the solver with these added lemmas.
      current_index_set.clear();
      update_index_set(cur);
      cur.clear();
      add_instantiations();

      if(current_index_set.empty())
      {
        debug() << "current index set is empty" << eom;
        return D_SATISFIABLE;
      }

      display_index_set();
      debug()<< "instantiating NOT_CONTAINS constraints" << eom;
      for(unsigned i=0; i<not_contains_axioms.size(); i++)
      {
        debug()<< "constraint " << i << eom;
        std::list<exprt> lemmas;
        instantiate_not_contains(not_contains_axioms[i], lemmas);
        for(const exprt &lemma : lemmas)
          add_lemma(lemma);
      }
      break;
    default:
      return res;
    }
  }
  debug() << "string_refinementt::dec_solve reached the maximum number"
           << "of steps allowed" << eom;
  return D_ERROR;
}

/// fills as many 0 as necessary in the bit vectors to have the right width
/// \par parameters: a Boolean and a expression with the desired type
/// \return a bit vector
bvt string_refinementt::convert_bool_bv(const exprt &boole, const exprt &orig)
{
  bvt ret;
  ret.push_back(convert(boole));
  size_t width=boolbv_width(orig.type());
  ret.resize(width, const_literal(false));
  return ret;
}

/// add the given lemma to the solver
/// \par parameters: a lemma
void string_refinementt::add_lemma(const exprt &lemma, bool add_to_index_set)
{
  if(!seen_instances.insert(lemma).second)
    return;

  if(lemma.is_true())
  {
    debug() << "string_refinementt::add_lemma : tautology" << eom;
    return;
  }

  debug() << "adding lemma " << from_expr(lemma) << eom;

  prop.l_set_to_true(convert(lemma));
  if(add_to_index_set)
    cur.push_back(lemma);
}

/// convert the content of a string to a more readable representation. This
/// should only be used for debbuging.
/// \par parameters: a constant array expression and a integer expression
/// \return a string
std::string string_refinementt::string_of_array(
  const exprt &arr, const exprt &size) const
{
  if(size.id()!=ID_constant)
    return "string of unknown size";
  unsigned n;
  if(to_unsigned_integer(to_constant_expr(size), n))
    n=0;

  if(n>MAX_CONCRETE_STRING_SIZE)
    return "very long string";
  if(n==0)
    return "\"\"";

  std::ostringstream buf;
  buf << "\"";
  exprt val=get(arr);

  if(val.id()=="array-list")
  {
    for(size_t i=0; i<val.operands().size()/2; i++)
    {
      exprt index=val.operands()[i*2];
      unsigned idx;
      if(!to_unsigned_integer(to_constant_expr(index), idx))
      {
        if(idx<n)
        {
          exprt value=val.operands()[i*2+1];
          unsigned c;
          if(!to_unsigned_integer(to_constant_expr(value), c))
            buf << static_cast<char>(c);
        }
      }
    }
  }
  else
  {
    return "unable to get array-list";
  }

  buf << "\"";
  return buf.str();
}

/// gets a model of an array and put it in a certain form
/// \par parameters: an array expression and a integer expression
/// \return a string expression
exprt string_refinementt::get_array(const exprt &arr, const exprt &size)
{
  exprt val=get(arr);
  typet char_type=arr.type().subtype();
  typet index_type=size.type();

  if(val.id()=="array-list")
  {
    array_typet ret_type(char_type, infinity_exprt(index_type));
    exprt ret=array_of_exprt(from_integer(0, char_type), ret_type);

    for(size_t i=0; i<val.operands().size()/2; i++)
    {
      exprt index=val.operands()[i*2];
      assert(index.type()==index_type);
      exprt value=val.operands()[i*2+1];
      assert(value.type()==char_type);
      ret=with_exprt(ret, index, value);
    }
    return ret;
  }
  else
  {
    debug() << "unable to get array-list value of "
            << from_expr(val) << eom;
    return arr;
  }
}

/// return true if the current model satisfies all the axioms
/// \return a Boolean
bool string_refinementt::check_axioms()
{
  debug() << "string_refinementt::check_axioms: ==============="
          << "===========================================" << eom;
  debug() << "string_refinementt::check_axioms: build the"
          << " interpretation from the model of the prop_solver" << eom;
  replace_mapt fmodel;

  for(auto it : generator.symbol_to_string)
  {
    string_exprt refined=it.second;
    const exprt &econtent=refined.content();
    const exprt &elength=refined.length();

    exprt len=get(elength);
    exprt arr=get_array(econtent, len);

    fmodel[elength]=len;
    fmodel[econtent]=arr;
    debug() << it.first << "=" << from_expr(it.second)
            << " of length " << from_expr(len) <<" := " << eom
            << from_expr(get(econtent)) << eom
            << string_of_array(econtent, len) << eom;
  }

  for(auto it : generator.boolean_symbols)
  {
    debug() << "" << it.get_identifier() << " := "
            << from_expr(get(it)) << eom;
    fmodel[it]=get(it);
  }

  for(auto it : generator.index_symbols)
  {
    debug() << "" << it.get_identifier() << " := "
            << from_expr(get(it)) << eom;
    fmodel[it]=get(it);
  }

  // Maps from indexes of violated universal axiom to a witness of violation
  std::map<size_t, exprt> violated;

  debug() << "there are " << universal_axioms.size()
          << " universal axioms" << eom;
  for(size_t i=0; i<universal_axioms.size(); i++)
  {
    const string_constraintt &axiom=universal_axioms[i];

    exprt negaxiom=and_exprt(axiom.premise(), not_exprt(axiom.body()));
    replace_expr(fmodel, negaxiom);

    debug() << "negaxiom: " << from_expr(negaxiom) << eom;

    satcheck_no_simplifiert sat_check;
    supert solver(ns, sat_check);
    solver << negaxiom;

    switch(solver())
    {
    case decision_proceduret::D_SATISFIABLE:
      {
        exprt val=solver.get(axiom.univ_var());
        violated[i]=val;
      }
      break;
    case decision_proceduret::D_UNSATISFIABLE:
      break;
    default:
      throw "failure in checking axiom";
    }
  }

  // tells whether one of the not_contains constraint can be violated
  bool violated_not_contains=false;
  debug() << "there are " << not_contains_axioms.size()
          << " not_contains axioms" << eom;

  for(auto nc_axiom : not_contains_axioms)
  {
    typet index_type=nc_axiom.s0().length().type();
    exprt zero=from_integer(0, index_type);
    exprt witness=generator.get_witness_of(nc_axiom, zero);
    exprt val=get(witness);
    violated_not_contains=true;
  }

  if(violated.empty() && !violated_not_contains)
  {
    debug() << "no violated property" << eom;
    return true;
  }
  else
  {
    debug() << violated.size() << " string axioms can be violated" << eom;

    if(use_counter_example)
    {
      // Checking if the current solution satisfies the constraints
      for(const auto &v : violated)
      {
        const exprt &val=v.second;
        const string_constraintt &axiom=universal_axioms[v.first];

        exprt premise(axiom.premise());
        exprt body(axiom.body());
        implies_exprt instance(premise, body);
        replace_expr(axiom.univ_var(), val, instance);
        if(seen_instances.insert(instance).second)
          add_lemma(instance);
        else
          debug() << "instance already seen" << eom;
      }
    }

    return false;
  }
}

/// \par parameters: an expression with only addition and substraction
/// \return a map where each leaf of the input is mapped to the number of times
///   it is added. For instance, expression $x + x - y$ would give the map x ->
///   2, y -> -1.
std::map<exprt, int> string_refinementt::map_representation_of_sum(
  const exprt &f) const
{
  // number of time the leaf should be added (can be negative)
  std::map<exprt, int> elems;

  std::list<std::pair<exprt, bool> > to_process;
  to_process.push_back(std::make_pair(f, true));

  while(!to_process.empty())
  {
    exprt cur=to_process.back().first;
    bool positive=to_process.back().second;
    to_process.pop_back();
    if(cur.id()==ID_plus)
    {
      to_process.push_back(std::make_pair(cur.op1(), positive));
      to_process.push_back(std::make_pair(cur.op0(), positive));
    }
    else if(cur.id()==ID_minus)
    {
      to_process.push_back(std::make_pair(cur.op1(), !positive));
      to_process.push_back(std::make_pair(cur.op0(), positive));
    }
    else if(cur.id()==ID_unary_minus)
    {
      to_process.push_back(std::make_pair(cur.op0(), !positive));
    }
    else
    {
      if(positive)
        elems[cur]=elems[cur]+1;
      else
        elems[cur]=elems[cur]-1;
    }
  }
  return elems;
}

/// \par parameters: a map from expressions to integers
/// \return a expression for the sum of each element in the map a number of
///   times given by the corresponding integer in the map. For a map x -> 2, y
///   -> -1 would give an expression $x + x - y$.
exprt string_refinementt::sum_over_map(
  std::map<exprt, int> &m, bool negated) const
{
  exprt sum=nil_exprt();
  mp_integer constants=0;
  typet index_type;
  if(m.empty())
    return nil_exprt();
  else
    index_type=m.begin()->first.type();

  for(const auto &term : m)
  {
    // We should group constants together...
    const exprt &t=term.first;
    int second=negated?(-term.second):term.second;
    if(t.id()==ID_constant)
    {
      std::string value(to_constant_expr(t).get_value().c_str());
      constants+=binary2integer(value, true)*second;
    }
    else
    {
      switch(second)
      {
      case -1:
        if(sum.is_nil())
          sum=unary_minus_exprt(t);
        else
          sum=minus_exprt(sum, t);
        break;

      case 1:
        if(sum.is_nil())
          sum=t;
        else
          sum=plus_exprt(sum, t);
        break;

      default:
        if(second>1)
        {
          for(int i=0; i<second; i++)
            sum=plus_exprt(sum, t);
        }
        else
        {
          for(int i=0; i>second; i--)
            sum=minus_exprt(sum, t);
        }
      }
    }
  }

  exprt index_const=from_integer(constants, index_type);
  if(sum.is_not_nil())
    return plus_exprt(sum, index_const);
  else
    return index_const;
}

/// \par parameters: an expression with only plus and minus expr
/// \return an equivalent expression in a cannonical form
exprt string_refinementt::simplify_sum(const exprt &f) const
{
  std::map<exprt, int> map=map_representation_of_sum(f);
  return sum_over_map(map);
}

/// \par parameters: a symbol qvar, an expression val, an expression f
///   containing + and −
/// operations in which qvar should appear exactly once.
/// \return an expression corresponding of $f^{−1}(val)$ where $f$ is seen as
///   a function of $qvar$, i.e. the value that is necessary for qvar for f to
///   be equal to val. For instance, if `f` corresponds to the expression $q +
///   x$, `compute_inverse_function(q,v,f)` returns an expression for $v - x$.
exprt string_refinementt::compute_inverse_function(
  const exprt &qvar, const exprt &val, const exprt &f)
{
  exprt positive, negative;
  // number of time the element should be added (can be negative)
  // qvar has to be equal to val - f(0) if it appears positively in f
  // (ie if f(qvar)=f(0) + qvar) and f(0) - val if it appears negatively
  // in f. So we start by computing val - f(0).
  std::map<exprt, int> elems=map_representation_of_sum(minus_exprt(val, f));

  // true if qvar appears negatively in f (positively in elems):
  bool neg=false;

  auto it=elems.find(qvar);
  assert(it!=elems.end());
  if(it->second==1 || it->second==-1)
  {
    neg=(it->second==1);
  }
  else
  {
    assert(it->second==0);
    debug() << "in string_refinementt::compute_inverse_function:"
            << " warning: occurrences of qvar canceled out " << eom;
  }

  elems.erase(it);
  return sum_over_map(elems, neg);
}



class find_qvar_visitort: public const_expr_visitort
{
private:
  const exprt &qvar_;

public:
  bool found;

  explicit find_qvar_visitort(const exprt &qvar): qvar_(qvar), found(false) {}

  void operator()(const exprt &expr)
  {
    if(expr==qvar_)
      found=true;
  }
};

/// looks for the symbol and return true if it is found
/// \par parameters: an index expression and a symbol qvar
/// \return a Boolean
static bool find_qvar(const exprt index, const symbol_exprt &qvar)
{
  find_qvar_visitort v2(qvar);
  index.visit(v2);
  return v2.found;
}

/// add to the index set all the indices that appear in the formulas and the
/// upper bound minus one
/// \par parameters: a list of string constraints
void string_refinementt::initial_index_set(
  const std::vector<string_constraintt>  &string_axioms)
{
  for(const auto &axiom : string_axioms)
    initial_index_set(axiom);
}

/// add to the index set all the indices that appear in the formulas
/// \par parameters: a list of string constraints
void string_refinementt::update_index_set(const std::vector<exprt> &cur)
{
  for(const auto &axiom : cur)
    update_index_set(axiom);
}

/// add to the index set all the indices that appear in the formula and the
/// upper bound minus one
/// \par parameters: a string constraint
void string_refinementt::initial_index_set(const string_constraintt &axiom)
{
  symbol_exprt qvar=axiom.univ_var();
  std::list<exprt> to_process;
  to_process.push_back(axiom.body());

  while(!to_process.empty())
  {
    exprt cur=to_process.back();
    to_process.pop_back();
    if(cur.id()==ID_index)
    {
      const exprt &s=cur.op0();
      const exprt &i=cur.op1();

      bool has_quant_var=find_qvar(i, qvar);

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
        minus_exprt kminus1(
          axiom.upper_bound(),
          from_integer(1, axiom.upper_bound().type()));
        replace_expr(qvar, kminus1, e);
        current_index_set[s].insert(e);
        index_set[s].insert(e);
      }
    }
    else
      forall_operands(it, cur)
        to_process.push_back(*it);
  }
}

/// add to the index set all the indices that appear in the formula
/// \par parameters: a string constraint
void string_refinementt::update_index_set(const exprt &formula)
{
  std::list<exprt> to_process;
  to_process.push_back(formula);

  while(!to_process.empty())
  {
    exprt cur=to_process.back();
    to_process.pop_back();
    if(cur.id()==ID_index)
    {
      const exprt &s=cur.op0();
      const exprt &i=cur.op1();
      assert(s.type().id()==ID_array);
      exprt simplified=simplify_sum(i);
      if(index_set[s].insert(simplified).second)
      {
        debug() << "adding to index set of " << from_expr(s)
                << ": " << from_expr(simplified) << eom;
        current_index_set[s].insert(simplified);
      }
    }
    else
    {
      forall_operands(it, cur)
        to_process.push_back(*it);
    }
  }
}


// Will be used to visit an expression and return the index used
// with the given char array
class find_index_visitort: public const_expr_visitort
{
private:
  const exprt &str_;

public:
  explicit find_index_visitort(const exprt &str): str_(str) {}

  void operator()(const exprt &expr)
  {
    if(expr.id()==ID_index)
    {
      const index_exprt &i=to_index_expr(expr);
      if(i.array()==str_)
        throw i.index();
    }
  }
};

/// find an index used in the expression for str, for instance with arguments
/// (str[k] == 'a') and str, the function should return k
/// \par parameters: a formula expr and a char array str
/// \return an index expression
exprt find_index(const exprt &expr, const exprt &str)
{
  find_index_visitort v1(str);
  try
  {
    expr.visit(v1);
    return nil_exprt();
  }
  catch (exprt i) { return i; }
}


/// \par parameters: an universaly quantified formula `axiom`, an array of char
/// variable `str`, and an index expression `val`.
/// \return substitute `qvar` the universaly quantified variable of `axiom`, by
///   an index `val`, in `axiom`, so that the index used for `str` equals `val`.
///   For instance, if `axiom` corresponds to $\forall q. s[q+x]='a' &&
///   t[q]='b'$, `instantiate(axom,s,v)` would return an expression for
///   $s[v]='a' && t[v-x]='b'$.
exprt string_refinementt::instantiate(
  const string_constraintt &axiom, const exprt &str, const exprt &val)
{
  exprt idx=find_index(axiom.body(), str);
  if(idx.is_nil())
    return true_exprt();
  if(!find_qvar(idx, axiom.univ_var()))
    return true_exprt();

  exprt r=compute_inverse_function(axiom.univ_var(), val, idx);
  implies_exprt instance(axiom.premise(), axiom.body());
  replace_expr(axiom.univ_var(), r, instance);
  // We are not sure the index set contains only positive numbers
  exprt bounds=and_exprt(
    axiom.univ_within_bounds(),
    binary_relation_exprt(
      from_integer(0, val.type()), ID_le, val));
  replace_expr(axiom.univ_var(), r, bounds);
  return implies_exprt(bounds, instance);
}


void string_refinementt::instantiate_not_contains(
  const string_not_contains_constraintt &axiom, std::list<exprt> &new_lemmas)
{
  exprt s0=axiom.s0();
  exprt s1=axiom.s1();

  debug() << "instantiate not contains " << from_expr(s0) << " : "
          << from_expr(s1) << eom;
  expr_sett index_set0=index_set[to_string_expr(s0).content()];
  expr_sett index_set1=index_set[to_string_expr(s1).content()];

  for(auto it0 : index_set0)
    for(auto it1 : index_set1)
    {
      debug() << from_expr(it0) << " : " << from_expr(it1) << eom;
      exprt val=minus_exprt(it0, it1);
      exprt witness=generator.get_witness_of(axiom, val);
      and_exprt prem_and_is_witness(
        axiom.premise(),
        equal_exprt(witness, it1));

      not_exprt differ(
        equal_exprt(
          to_string_expr(s0)[it0],
          to_string_expr(s1)[it1]));
      exprt lemma=implies_exprt(prem_and_is_witness, differ);

      new_lemmas.push_back(lemma);
      // we put bounds on the witnesses:
      // 0 <= v <= |s0| - |s1| ==> 0 <= v+w[v] < |s0| && 0 <= w[v] < |s1|
      exprt zero=from_integer(0, val.type());
      binary_relation_exprt c1(zero, ID_le, plus_exprt(val, witness));
      binary_relation_exprt c2
        (to_string_expr(s0).length(), ID_gt, plus_exprt(val, witness));
      binary_relation_exprt c3(to_string_expr(s1).length(), ID_gt, witness);
      binary_relation_exprt c4(zero, ID_le, witness);

      minus_exprt diff(
        to_string_expr(s0).length(),
        to_string_expr(s1).length());

      and_exprt premise(
        binary_relation_exprt(zero, ID_le, val),
        binary_relation_exprt(diff, ID_ge, val));
      exprt witness_bounds=implies_exprt(
        premise,
        and_exprt(and_exprt(c1, c2), and_exprt(c3, c4)));
      new_lemmas.push_back(witness_bounds);
    }
}

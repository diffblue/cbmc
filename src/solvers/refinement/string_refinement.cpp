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
#include <iomanip>
#include <ansi-c/string_constant.h>
#include <util/cprover_prefix.h>
#include <util/replace_expr.h>
#include <util/refined_string_type.h>
#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/refinement/string_refinement_invariant.h>
#include <langapi/language_util.h>
#include <java_bytecode/java_types.h>

string_refinementt::string_refinementt(
  const namespacet &_ns,
  propt &_prop,
  unsigned refinement_bound):
  supert(_ns, _prop),
  use_counter_example(false),
  do_concretizing(false),
  initial_loop_bound(refinement_bound),
  non_empty_string(false)
{ }

/// Add constraints on the size of strings used in the program.
/// \param i: maximum length which is allowed for strings.
/// by default the strings length has no other limit
/// than the maximal integer according to the type of their
/// length, for instance 2^31-1 for Java.
void string_refinementt::set_max_string_length(size_t i)
{
  generator.max_string_length=i;
}

/// Add constraints on the size of nondet character arrays to ensure they have
/// length at least 1
void string_refinementt::enforce_non_empty_string()
{
  non_empty_string=true;
}

/// Add constraints on characters used in the program to ensure they are
/// printable
void string_refinementt::enforce_printable_characters()
{
  generator.force_printable_characters=true;
}

/// display the current index set, for debugging
void string_refinementt::display_index_set()
{
  std::size_t count=0;
  std::size_t count_current=0;
  for(const auto &i : index_set)
  {
    const exprt &s=i.first;
    debug() << "IS(" << from_expr(ns, "", s) << ")=={" << eom;

    for(auto j : i.second)
    {
      if(current_index_set[i.first].find(j)!=current_index_set[i.first].end())
      {
        count_current++;
        debug() << "**";
      }
      debug() << "  " << from_expr(ns, "", j) << ";" << eom;
      count++;
    }
    debug() << "}"  << eom;
  }
  debug() << count << " elements in index set (" << count_current
          << " newly added)" << eom;
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
    debug() << "IS(" << from_expr(ns, "", s) << ")=={";

    for(const auto &j : i.second)
      debug() << from_expr(ns, "", j) << "; ";
    debug() << "}"  << eom;

    for(const auto &ua : universal_axioms)
    {
      for(const auto &j : i.second)
      {
        exprt lemma=instantiate(ua, s, j);
        add_lemma(lemma);
      }
    }
  }
}

/// List the simple expressions on which the expression depends in the
/// `symbol_resolve` map. A simple expression is either a symbol or a
/// constant array
/// \param expr: an expression
static void depends_in_symbol_map(const exprt &expr, std::vector<exprt> &accu)
{
  if(expr.id()==ID_if)
  {
    if_exprt if_expr=to_if_expr(expr);
    depends_in_symbol_map(if_expr.true_case(), accu);
    depends_in_symbol_map(if_expr.false_case(), accu);
  }
  else if(expr.id()==ID_struct)
  {
    string_exprt str=to_string_expr(expr);
    depends_in_symbol_map(str.content(), accu);
  }
  else
  {
    INVARIANT(
      expr.id()==ID_symbol || expr.id()==ID_array || expr.id()==ID_array_of,
      "leaf in symbol resolve should be a symbol or a constant array");
    accu.push_back(expr);
  }
}

/// keeps a map of symbols to expressions, such as none of the mapped values
/// exist as a key
/// \param lhs: a symbol expression
/// \param rhs: an expression to map it to, which should be either a symbol
///             a string_exprt, an array_exprt, an array_of_exprt or an
///             if_exprt with branches of the previous kind
void string_refinementt::add_symbol_to_symbol_map(
  const exprt &lhs, const exprt &rhs)
{
  PRECONDITION(lhs.id()==ID_symbol);
  PRECONDITION(rhs.id()==ID_symbol ||
               rhs.id()==ID_array ||
               rhs.id()==ID_array_of ||
               rhs.id()==ID_if ||
               (rhs.id()==ID_struct &&
                refined_string_typet::is_refined_string_type(rhs.type())));

  // We insert the mapped value of the rhs, if it exists.
  auto it=symbol_resolve.find(rhs);
  const exprt &new_rhs=it!=symbol_resolve.end()?it->second:rhs;
  symbol_resolve[lhs]=new_rhs;

  // List the leaves of new_rhs
  std::vector<exprt> leaves;
  depends_in_symbol_map(new_rhs, leaves);

  const auto &symbols_to_update_with_new_rhs=reverse_symbol_resolve[lhs];

  // We need to update all the symbols which depend on lhs
  for(const exprt &item : symbols_to_update_with_new_rhs)
    replace_expr(symbol_resolve, symbol_resolve[item]);

  // Every time a symbol at the leaves is updated we need to update lhs
  // and the symbols that depend on it
  for(const auto &leaf : leaves)
  {
    reverse_symbol_resolve[leaf].push_back(lhs);
    for(const exprt &item : symbols_to_update_with_new_rhs)
      reverse_symbol_resolve[leaf].push_back(item);
  }
}

/// add axioms if the rhs is a character array
/// \par parameters: the rhs and lhs of an equality over character arrays
void string_refinementt::set_char_array_equality(
  const exprt &lhs, const exprt &rhs)
{
  PRECONDITION(lhs.id()==ID_symbol);

  if(rhs.id()==ID_array && rhs.type().id()==ID_array)
  {
    const typet &index_type=to_array_type(rhs.type()).size().type();
    for(size_t i=0, ilim=rhs.operands().size(); i!=ilim; ++i)
    {
      // Introduce axioms to map symbolic rhs to its char array.
      index_exprt arraycell(rhs, from_integer(i, index_type));
      equal_exprt arrayeq(arraycell, rhs.operands()[i]);
      add_lemma(arrayeq, false);
    }
  }
  // At least for Java (as it is currently pre-processed), we need not consider
  // other cases, because all character arrays find themselves on the rhs of an
  // equality. Note that this might not be the case for other languages.
}

/// remove functions applications and create the necessary axioms
/// \par parameters: an expression containing function applications
/// \return an epression containing no function application
exprt string_refinementt::substitute_function_applications(exprt expr)
{
  for(size_t i=0; i<expr.operands().size(); ++i)
  {
    // TODO: only copy when necessary
    exprt op(expr.operands()[i]);
    expr.operands()[i]=substitute_function_applications(op);
  }

  if(expr.id()==ID_function_application)
  {
    function_application_exprt f=to_function_application_expr(expr);
    return generator.add_axioms_for_function_application(f);
  }

  return expr;
}

/// distinguish char array from other types
///
/// TODO: this is only for java char array and does not work for other languages
/// \param type: a type
/// \return true if the given type is an array of java characters
bool string_refinementt::is_char_array(const typet &type) const
{
  if(type.id()==ID_symbol)
    return is_char_array(ns.follow(type));

  return (type.id()==ID_array && type.subtype()==java_char_type());
}

/// add lemmas to the solver corresponding to the given equation
/// \param lhs: left hand side of an equality expression
/// \param rhs: right and side of the equality
/// \return true if the assignemnt needs to be handled by the parent class
///         via `set_to`
bool string_refinementt::add_axioms_for_string_assigns(
  const exprt &lhs, const exprt &rhs)
{
  if(is_char_array(rhs.type()))
  {
    set_char_array_equality(lhs, rhs);
    if(rhs.id() == ID_symbol || rhs.id() == ID_array)
    {
      add_symbol_to_symbol_map(lhs, rhs);
      return false;
    }
    else if(rhs.id()==ID_nondet_symbol)
    {
      add_symbol_to_symbol_map(
        lhs, generator.fresh_symbol("nondet_array", lhs.type()));
      return false;
    }
    else if(rhs.id()==ID_if)
    {
      add_symbol_to_symbol_map(lhs, rhs);
      return true;
    }
    else
    {
      warning() << "ignoring char array " << from_expr(ns, "", rhs) << eom;
      return true;
    }
  }
  if(refined_string_typet::is_refined_string_type(rhs.type()))
  {
    exprt refined_rhs=generator.add_axioms_for_refined_string(rhs);
    add_symbol_to_symbol_map(lhs, refined_rhs);
    return false;
  }
  // Other cases are to be handled by supert::set_to.
  return true;
}

/// If the expression is of type string, then adds constants to the index set to
/// force the solver to pick concrete values for each character, and fill the
/// maps `found_length` and `found_content`.
///
///          The way this is done is by looking for the length of the string,
///          then for each `i` in the index set, look at the value found by
///          the solver and put it in the `result` table.
///          For indexes that are not present in the index set, we put the
///          same value as the next index that is present in the index set.
///          We do so by traversing the array backward, remembering the
///          last value that has been initialized.
void string_refinementt::concretize_string(const exprt &expr)
{
  if(refined_string_typet::is_refined_string_type(expr.type()))
  {
    string_exprt str=to_string_expr(expr);
    exprt length=get(str.length());
    exprt content=str.content();
    replace_expr(symbol_resolve, content);
    found_length[content]=length;
    mp_integer found_length;
    if(!to_integer(length, found_length))
    {
      INVARIANT(
        found_length.is_long(),
        string_refinement_invariantt("the length of a string should be a "
          "long"));
      INVARIANT(
        found_length>=0,
        string_refinement_invariantt("the length of a string should be >= 0"));
      size_t concretize_limit=found_length.to_long();
      INVARIANT(
        concretize_limit<=generator.max_string_length,
        string_refinement_invariantt("string length must be less than the max "
          "length"));
      exprt content_expr=str.content();
      std::vector<exprt> result;

      if(index_set[str.content()].empty())
        return;

      // Use the last index as the default character value
      exprt last_concretized=simplify_expr(
        get(str[minus_exprt(length, from_integer(1, length.type()))]), ns);
      result.resize(concretize_limit, last_concretized);

      // Keep track of the indexes for which we have actual values
      std::set<size_t> initialized;

      for(const auto &i : index_set[str.content()])
      {
        mp_integer mp_index;
        exprt simple_i=simplify_expr(get(i), ns);
        if(to_integer(simple_i, mp_index) ||
           mp_index<0 ||
           mp_index>=concretize_limit)
        {
          debug() << "concretize_string: ignoring out of bound index: "
                  << from_expr(ns, "", simple_i) << eom;
        }
        else
        {
          // Add an entry in the result vector
          size_t index=mp_index.to_long();
          exprt str_i=simplify_expr(str[simple_i], ns);
          exprt value=simplify_expr(get(str_i), ns);
          result[index]=value;
          initialized.insert(index);
        }
      }

      // Pad the concretized values to the left to assign the uninitialized
      // values of result. The indices greater than concretize_limit are
      // already assigned to last_concretized.
      pad_vector(result, initialized, last_concretized);

      array_exprt arr(to_array_type(content.type()));
      arr.operands()=result;
      debug() << "Concretized " << from_expr(ns, "", content_expr)
              << " = " << from_expr(ns, "", arr) << eom;
      found_content[content]=arr;
    }
  }
}

/// For each string whose length has been solved, add constants to the index set
/// to force the solver to pick concrete values for each character, and fill the
/// map `found_length`
void string_refinementt::concretize_results()
{
  for(const auto &it : symbol_resolve)
    concretize_string(it.second);
  for(const auto &it : generator.created_strings)
    concretize_string(it);
  add_instantiations();
}

/// For each string whose length has been solved, add constants to the map
/// `found_length`
void string_refinementt::concretize_lengths()
{
  for(const auto &it : symbol_resolve)
  {
    if(refined_string_typet::is_refined_string_type(it.second.type()))
    {
      string_exprt str=to_string_expr(it.second);
      exprt length=get(str.length());
      exprt content=str.content();
      replace_expr(symbol_resolve, content);
      found_length[content]=length;
     }
  }
  for(const auto &it : generator.created_strings)
  {
    if(refined_string_typet::is_refined_string_type(it.type()))
    {
      string_exprt str=to_string_expr(it);
      exprt length=get(str.length());
      exprt content=str.content();
      replace_expr(symbol_resolve, content);
      found_length[content]=length;
     }
  }
}

/// add lemmas representing the setting of an expression to a given value
/// \par parameters: an expression and the value to set it to
void string_refinementt::set_to(const exprt &expr, bool value)
{
  INVARIANT(
    equality_propagation,
    string_refinement_invariantt("set_to should only be called when equality "
      "propagation is enabled"));

  if(expr.id()==ID_equal)
  {
    equal_exprt eq_expr=to_equal_expr(expr);

    if(eq_expr.lhs().type()!=eq_expr.rhs().type())
    {
      warning() << "ignoring " << from_expr(ns, "", expr)
                << " [inconsistent types]" << eom;
      debug() << "lhs has type: " << eq_expr.lhs().type().pretty(12) << eom;
      debug() << "rhs has type: " << eq_expr.rhs().type().pretty(12) << eom;
      return;
    }

    if(expr.type().id()!=ID_bool)
    {
      error() << "string_refinementt::set_to got non-boolean operand: "
              << expr.pretty() << eom;
      INVARIANT(
        false,
        string_refinement_invariantt("set_to should only be called with exprs "
          "of type bool"));
    }

    // Preprocessing to remove function applications.
    const exprt &lhs=eq_expr.lhs();
    debug() << "(sr::set_to) " << from_expr(ns, "", lhs)
            << " = " << from_expr(ns, "", eq_expr.rhs()) << eom;

    // TODO: See if this happens at all.
    if(lhs.id()!=ID_symbol)
    {
      warning() << "ignoring " << from_expr(ns, "", expr) << eom;
      return;
    }

    exprt subst_rhs=substitute_function_applications(eq_expr.rhs());
    if(eq_expr.lhs().type()!=subst_rhs.type())
    {
      if(eq_expr.lhs().type().id() != ID_array ||
         subst_rhs.type().id() != ID_array ||
         eq_expr.lhs().type().subtype() != subst_rhs.type().subtype())
      {
        warning() << "ignoring " << from_expr(ns, "", expr)
                  << " [inconsistent types after substitution]" << eom;
        return;
      }
      else
      {
        debug() << "(sr::set_to) accepting arrays with "
                << "same subtype but different sizes" << eom;
      }
    }

    if(value)
    {
      if(!add_axioms_for_string_assigns(lhs, subst_rhs))
        return;
    }
    else
    {
      // TODO: Something should also be done if value is false.
      INVARIANT(
        !is_char_array(eq_expr.rhs().type()),
        string_refinement_invariantt("set_to cannot set a char_array"));
      INVARIANT(
        !refined_string_typet::is_refined_string_type(eq_expr.rhs().type()),
        string_refinement_invariantt("set_to cannot set a refined_string"));
    }

    non_string_axioms.push_back(std::make_pair(equal_exprt(lhs, subst_rhs),
                                               value));
  }
  // We keep a list of the axioms to give to supert::set_to in order to
  // substitute the symbols in dec_solve().
  else
    non_string_axioms.push_back(std::make_pair(expr, value));
}

/// use a refinement loop to instantiate universal axioms, call the sat solver,
/// and instantiate more indexes if needed.
/// \return result of the decision procedure
decision_proceduret::resultt string_refinementt::dec_solve()
{
  // Substitute all symbols to char arrays in the axioms to give to
  // supert::set_to().
  for(std::pair<exprt, bool> &pair : non_string_axioms)
  {
    replace_expr(symbol_resolve, pair.first);
    debug() << "super::set_to " << from_expr(ns, "", pair.first) << eom;
    supert::set_to(pair.first, pair.second);
  }

  for(exprt &axiom : generator.axioms)
  {
    replace_expr(symbol_resolve, axiom);
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
  }

  found_length.clear();
  found_content.clear();

  // Initial try without index set
  decision_proceduret::resultt res=supert::dec_solve();
  if(res==resultt::D_SATISFIABLE)
  {
    if(!check_axioms())
    {
      debug() << "check_SAT: got SAT but the model is not correct" << eom;
    }
    else
    {
      debug() << "check_SAT: the model is correct" << eom;
      concretize_lengths();
      return resultt::D_SATISFIABLE;
    }
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
    case resultt::D_SATISFIABLE:
      if(!check_axioms())
      {
        debug() << "check_SAT: got SAT but the model is not correct" << eom;
      }
      else
      {
        debug() << "check_SAT: the model is correct" << eom;
        concretize_lengths();
        return resultt::D_SATISFIABLE;
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
        if(do_concretizing)
        {
          concretize_results();
          return resultt::D_SATISFIABLE;
        }
        else
        {
          debug() << "check_SAT: the model is correct and "
                  << "does not need concretizing" << eom;
          return resultt::D_SATISFIABLE;
        }
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
      debug() << "check_SAT: default return " << static_cast<int>(res) << eom;
      return res;
    }
  }
  debug() << "string_refinementt::dec_solve reached the maximum number"
           << "of steps allowed" << eom;
  return resultt::D_ERROR;
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
/// \par parameters: a lemma and Boolean value stating whether the lemma should
/// be added to the index set.
void string_refinementt::add_lemma(
  const exprt &lemma, bool _simplify, bool add_to_index_set)
{
  if(!seen_instances.insert(lemma).second)
    return;

  if(add_to_index_set)
    cur.push_back(lemma);

  exprt simple_lemma=lemma;
  if(_simplify)
    simplify(simple_lemma, ns);

  if(simple_lemma.is_true())
  {
#if 0
    debug() << "string_refinementt::add_lemma : tautology" << eom;
#endif
    return;
  }

  debug() << "adding lemma " << from_expr(ns, "", simple_lemma) << eom;

  prop.l_set_to_true(convert(simple_lemma));
}

/// get a model of an array and put it in a certain form. If the size cannot be
/// obtained or if it is too big, return an empty array.
/// \par parameters: an expression representing an array and an expression
/// representing an integer
/// \return an array expression or an array_of_exprt
exprt string_refinementt::get_array(const exprt &arr, const exprt &size) const
{
  exprt arr_val=get_array(arr);
  exprt size_val=supert::get(size);
  size_val=simplify_expr(size_val, ns);
  typet char_type=arr.type().subtype();
  typet index_type=size.type();
  array_typet empty_ret_type(char_type, from_integer(0, index_type));
  array_of_exprt empty_ret(from_integer(0, char_type), empty_ret_type);

  if(size_val.id()!=ID_constant)
  {
#if 0
    debug() << "(sr::get_array) string of unknown size: "
            << from_expr(ns, "", size_val) << eom;
#endif
    return empty_ret;
  }

  unsigned n;
  if(to_unsigned_integer(to_constant_expr(size_val), n))
  {
#if 0
    debug() << "(sr::get_array) size is not valid" << eom;
#endif
    return empty_ret;
  }

  array_typet ret_type(char_type, from_integer(n, index_type));
  array_exprt ret(ret_type);

  if(n>generator.max_string_length)
  {
#if 0
    debug() << "(sr::get_array) long string (size=" << n << ")" << eom;
#endif
    return empty_ret;
  }

  if(n==0)
  {
#if 0
    debug() << "(sr::get_array) empty string" << eom;
#endif
    return empty_ret;
  }

  std::vector<unsigned> concrete_array(n);

  if(arr_val.id()=="array-list")
  {
    std::set<unsigned> initialized;
    for(size_t i=0; i<arr_val.operands().size()/2; i++)
    {
      exprt index=arr_val.operands()[i*2];
      unsigned idx;
      if(!to_unsigned_integer(to_constant_expr(index), idx))
      {
        if(idx<n)
        {
          exprt value=arr_val.operands()[i*2+1];
          to_unsigned_integer(to_constant_expr(value), concrete_array[idx]);
          initialized.insert(idx);
        }
      }
    }

    // Pad the concretized values to the left to assign the uninitialized
    // values of result.
    pad_vector(concrete_array, initialized, concrete_array[n-1]);
  }
  else if(arr_val.id()==ID_array)
  {
    for(size_t i=0; i<arr_val.operands().size() && i<n; i++)
    {
      unsigned c;
      exprt op=arr_val.operands()[i];
      if(op.id()==ID_constant)
      {
        to_unsigned_integer(to_constant_expr(op), c);
        concrete_array[i]=c;
      }
    }
  }
  else
  {
#if 0
    debug() << "unable to get array-list value of " << from_expr(ns, "", arr)
            << " of size " << n << eom;
#endif
    return array_of_exprt(from_integer(0, char_type), ret_type);
  }

  for(size_t i=0; i<n; i++)
  {
    exprt c_expr=from_integer(concrete_array[i], char_type);
    ret.move_to_operands(c_expr);
  }

  return ret;
}


/// get a model of an array of unknown size and infer the size if possible
/// \par parameters: an expression representing an array
/// \return an expression
exprt string_refinementt::get_array(const exprt &arr) const
{
  exprt arr_model=supert::get(arr);
  if(arr_model.id()==ID_array)
  {
    array_typet &arr_type=to_array_type(arr_model.type());
    arr_type.size()=from_integer(
      arr_model.operands().size(), arr_type.size().type());
  }
  return arr_model;
}

/// convert the content of a string to a more readable representation. This
/// should only be used for debbuging.
/// \par parameters: a constant array expression and a integer expression
/// \return a string
std::string string_refinementt::string_of_array(const array_exprt &arr)
{
  unsigned n;
  if(arr.type().id()!=ID_array)
      return std::string("");

  exprt size_expr=to_array_type(arr.type()).size();
  PRECONDITION(size_expr.id()==ID_constant);
  to_unsigned_integer(to_constant_expr(size_expr), n);
  std::string str(n, '?');

  std::ostringstream result;
  std::locale loc;

  for(size_t i=0; i<arr.operands().size() && i<n; i++)
  {
    // TODO: factorize with utf16_little_endian_to_ascii
    unsigned c;
    exprt arr_i=arr.operands()[i];
    PRECONDITION(arr_i.id()==ID_constant);
    to_unsigned_integer(to_constant_expr(arr_i), c);
    if(c<=255 && c>=32)
      result << (unsigned char) c;
    else
    {
      result << "\\u" << std::hex << std::setw(4) << std::setfill('0')
             << (unsigned int) c;
    }
  }

  return result.str();
}

/// Display part of the current model by mapping the variables created by the
/// solver to constant expressions given by the current model
void string_refinementt::debug_model()
{
  const std::string indent("  ");
  for(auto it : symbol_resolve)
  {
    if(refined_string_typet::is_refined_string_type(it.second.type()))
    {
      debug() << "- " << from_expr(ns, "", to_symbol_expr(it.first)) << ":\n";
      string_exprt refined=to_string_expr(it.second);
      debug() << indent << indent << "in_map: "
              << from_expr(ns, "", refined) << eom;
      debug() << indent << indent << "resolved: "
              << from_expr(ns, "", refined) << eom;
      const exprt &econtent=refined.content();
      const exprt &elength=refined.length();

      exprt len=supert::get(elength);
      len=simplify_expr(len, ns);
      exprt arr=get_array(econtent, len);
      if(arr.id()==ID_array)
        debug() << indent << indent << "as_string: \""
                << string_of_array(to_array_expr(arr)) << "\"\n";
      else
        debug() << indent << indent << "as_char_array: "
                << from_expr(ns, "", arr) << "\n";

      debug() << indent << indent << "size: " << from_expr(ns, "", len) << eom;
    }
    else
    {
      INVARIANT(
        is_char_array(it.second.type()),
        string_refinement_invariantt("symbol_resolve should only map to "
          "refined_strings or to char_arrays, and refined_strings are already "
          "handled"));
      exprt arr=it.second;
      replace_expr(symbol_resolve, arr);
      debug() << "- " << from_expr(ns, "", to_symbol_expr(it.first)) << ":\n";
      debug() << indent << indent << "resolved: "
              << from_expr(ns, "", arr) << "\n";
      exprt arr_model=get_array(arr);
      debug() << indent << indent << "char_array: "
              << from_expr(ns, "", arr_model) << eom;
    }
  }

  for(auto it : generator.boolean_symbols)
  {
      debug() << " - " << it.get_identifier() << ": "
              << from_expr(ns, "", supert::get(it)) << eom;
  }

  for(auto it : generator.index_symbols)
  {
     debug() << " - " << it.get_identifier() << ": "
             << from_expr(ns, "", supert::get(it)) << eom;
  }
}

/// Create a new expression where 'with' expressions on arrays are replaced by
/// 'if' expressions. e.g. for an array access arr[x], where: `arr :=
/// array_of(12) with {0:=24} with {2:=42}` the constructed expression will be:
/// `index==0 ? 24 : index==2 ? 42 : 12`
/// \param expr: A (possibly nested) 'with' expression on an `array_of`
///   expression
/// \param index: An index with which to build the equality condition
/// \return An expression containing no 'with' expression
exprt string_refinementt::substitute_array_with_expr(
  const exprt &expr, const exprt &index) const
{
  if(expr.id()==ID_with)
  {
    const with_exprt &with_expr=to_with_expr(expr);
    const exprt &then_expr=with_expr.new_value();
    exprt else_expr=substitute_array_with_expr(with_expr.old(), index);
    const typet &type=then_expr.type();
    CHECK_RETURN(else_expr.type()==type);
    return if_exprt(
      equal_exprt(index, with_expr.where()), then_expr, else_expr, type);
  }
  else
  {
    // Only handle 'with' expressions and 'array_of' expressions.
    INVARIANT(
      expr.id()==ID_array_of,
      string_refinement_invariantt("only handles 'with' and 'array_of' "
        "expressions, and expr is 'with' is handled above"));
    return to_array_of_expr(expr).what();
  }
}

/// create an equivalent expression where array accesses and 'with' expressions
/// are replaced by 'if' expressions, in particular:
///  * for an array access `arr[x]`, where:
///    `arr := {12, 24, 48}` the constructed expression will be:
///    `index==0 ? 12 : index==1 ? 24 : 48`
///  * for an array access `arr[x]`, where:
///    `arr := array_of(12) with {0:=24} with {2:=42}` the constructed
///    expression will be: `index==0 ? 24 : index==2 ? 42 : 12`
///  * for an array access `(g1?arr1:arr2)[x]` where `arr1 := {12}` and
///    `arr2 := {34}`, the constructed expression will be: `g1 ? 12 : 34`
/// \param expr: an expression containing array accesses
/// \return an expression containing no array access
void string_refinementt::substitute_array_access(exprt &expr) const
{
  for(auto &op : expr.operands())
    substitute_array_access(op);

  if(expr.id()==ID_index)
  {
    index_exprt &index_expr=to_index_expr(expr);

    if(index_expr.array().id()==ID_symbol)
    {
      expr=index_expr;
      return;
    }

    if(index_expr.array().id()==ID_with)
    {
      expr=substitute_array_with_expr(
        index_expr.array(), index_expr.index());
      return;
    }

    if(index_expr.array().id()==ID_array_of)
    {
      expr=to_array_of_expr(index_expr.array()).op();
      return;
    }

    if(index_expr.array().id()==ID_if)
    {
      // Substitute recursively in branches of conditional expressions
      if_exprt if_expr=to_if_expr(index_expr.array());
      exprt true_case=index_exprt(if_expr.true_case(), index_expr.index());
      substitute_array_access(true_case);
      exprt false_case=index_exprt(if_expr.false_case(), index_expr.index());
      substitute_array_access(false_case);
      expr=if_exprt(if_expr.cond(), true_case, false_case);
      return;
    }

    DATA_INVARIANT(
      index_expr.array().id()==ID_array,
      string_refinement_invariantt("and index expression must be on a symbol, "
        "with, array_of, if, or array, and all cases besides array are handled "
        "above"));
    array_exprt &array_expr=to_array_expr(index_expr.array());

    INVARIANT(
      !array_expr.operands().empty(),
      string_refinement_invariantt("the array expression should not be empty"));
    size_t last_index=array_expr.operands().size()-1;

    const typet &char_type=index_expr.array().type().subtype();
    exprt ite=array_expr.operands().back();

    if(ite.type()!=char_type)
    {
      // We have to manually set the type for unknown values
      INVARIANT(
        ite.id()==ID_unknown,
        string_refinement_invariantt("the last element can only have type char "
          "or unknown, and it is not char type"));
      ite.type()=char_type;
    }

    auto op_it=++array_expr.operands().rbegin();

    for(size_t i=last_index-1;
        op_it!=array_expr.operands().rend(); ++op_it, --i)
    {
      equal_exprt equals(index_expr.index(), from_integer(i, java_int_type()));
      if(op_it->type()!=char_type)
      {
        INVARIANT(
          op_it->id()==ID_unknown,
          string_refinement_invariantt("elements can only have type char or "
            "unknown, and it is not char type"));
        op_it->type()=char_type;
      }
      ite=if_exprt(equals, *op_it, ite);
    }
    expr=ite;
  }
}

/// Negates the constraint to be fed to a solver. The intended usage is to find
/// an assignement of the universal variable that would violate the axiom. To
/// avoid false positives, the symbols other than the universal variable should
/// have been replaced by their valuation in the current model.
/// \pre Symbols other than the universal variable should have been replaced by
///   their valuation in the current model.
/// \param axiom: the not_contains constraint to add the negation of
/// \param val: the existential witness for the axiom
/// \param univ_var: the universal variable for the negation of the axiom
/// \return: the negation of the axiom under the current evaluation
exprt string_refinementt::negation_of_not_contains_constraint(
  const string_not_contains_constraintt &axiom,
  const exprt &val,
  const symbol_exprt &univ_var)
{
  exprt lbu=axiom.univ_lower_bound();
  exprt ubu=axiom.univ_upper_bound();
  if(lbu.id()==ID_constant && ubu.id()==ID_constant)
  {
    mp_integer lb_int, ub_int;
    to_integer(to_constant_expr(lbu), lb_int);
    to_integer(to_constant_expr(ubu), ub_int);
    if(ub_int<=lb_int)
    {
      debug() << "empty constraint with current model" << eom;
      return false_exprt();
    }
  }

  exprt lbe=axiom.exists_lower_bound();
  exprt ube=axiom.exists_upper_bound();

  if(axiom.premise()==false_exprt())
  {
    debug() << "(string_refinement::check_axioms) adding false" << eom;
    return false_exprt();
  }

  // Witness is the Skolem function for the existential, which we evaluate at
  // univ_var.
  and_exprt univ_bounds(
    binary_relation_exprt(lbu, ID_le, univ_var),
    binary_relation_exprt(ubu, ID_gt, univ_var));
  and_exprt exists_bounds(
    binary_relation_exprt(lbe, ID_le, val),
    binary_relation_exprt(ube, ID_gt, val));
  equal_exprt equal_chars(
    axiom.s0()[plus_exprt(univ_var, val)],
    axiom.s1()[val]);
  and_exprt negaxiom(univ_bounds, axiom.premise(), exists_bounds, equal_chars);

  debug() << "(sr::check_axioms) negated not_contains axiom: "
          << from_expr(ns, "", negaxiom) << eom;
  substitute_array_access(negaxiom);
  return negaxiom;
}

/// Negates the constraint to be fed to a solver. The intended usage is to find
/// an assignement of the universal variable that would violate the axiom. To
/// avoid false positives, the symbols other than the universal variable should
/// have been replaced by their valuation in the current model.
/// \pre Symbols other than the universal variable should have been replaced by
///   their valuation in the current model.
/// \param axiom: the not_contains constraint to add the negation of
/// \return: the negation of the axiom under the current evaluation
exprt string_refinementt::negation_of_constraint(
  const string_constraintt &axiom)
{
  exprt lb=axiom.lower_bound();
  exprt ub=axiom.upper_bound();
  if(lb.id()==ID_constant && ub.id()==ID_constant)
  {
    mp_integer lb_int, ub_int;
    to_integer(to_constant_expr(lb), lb_int);
    to_integer(to_constant_expr(ub), ub_int);
    if(ub_int<=lb_int)
    {
      debug() << "empty constraint with current model" << eom;
      return false_exprt();
    }
  }

  if(axiom.premise()==false_exprt())
  {
    debug() << "(string_refinement::check_axioms) adding false" << eom;
    return false_exprt();
  }

  and_exprt premise(axiom.premise(), axiom.univ_within_bounds());
  and_exprt negaxiom(premise, not_exprt(axiom.body()));

  debug() << "(sr::check_axioms) negated axiom: "
          << from_expr(ns, "", negaxiom) << eom;
  substitute_array_access(negaxiom);
  return negaxiom;
}

/// return true if the current model satisfies all the axioms
/// \return a Boolean
bool string_refinementt::check_axioms()
{
  debug() << "string_refinementt::check_axioms: ==============="
          << "===========================================" << eom;
  debug() << "string_refinementt::check_axioms: build the"
          << " interpretation from the model of the prop_solver" << eom;
  debug_model();

  // Maps from indexes of violated universal axiom to a witness of violation
  std::map<size_t, exprt> violated;

  debug() << "there are " << universal_axioms.size()
          << " universal axioms" << eom;
  for(size_t i=0; i<universal_axioms.size(); i++)
  {
    const string_constraintt &axiom=universal_axioms[i];
    const symbol_exprt univ_var=axiom.univ_var();
    const exprt bound_inf=axiom.lower_bound();
    const exprt bound_sup=axiom.upper_bound();
    const exprt prem=axiom.premise();
    const exprt body=axiom.body();

    const string_constraintt axiom_in_model(
      univ_var, get(bound_inf), get(bound_sup), get(prem), get(body));

    const exprt negaxiom=negation_of_constraint(axiom_in_model);
    exprt witness;

    bool is_sat=is_axiom_sat(negaxiom, univ_var, witness);

    if(is_sat)
    {
      debug() << "string constraint can be violated for "
              << univ_var.get_identifier()
              << " = " << from_expr(ns, "", witness) << eom;
      violated[i]=witness;
    }
  }

  // Maps from indexes of violated not_contains axiom to a witness of violation
  std::map<std::size_t, exprt> violated_not_contains;

  debug() << "there are " << not_contains_axioms.size()
          << " not_contains axioms" << eom;
  for(size_t i=0; i<not_contains_axioms.size(); i++)
  {
    const string_not_contains_constraintt &nc_axiom=not_contains_axioms[i];
    const exprt univ_bound_inf=nc_axiom.univ_lower_bound();
    const exprt univ_bound_sup=nc_axiom.univ_upper_bound();
    const exprt prem=nc_axiom.premise();
    const exprt exists_bound_inf=nc_axiom.exists_lower_bound();
    const exprt exists_bound_sup=nc_axiom.exists_upper_bound();
    const string_exprt s0=nc_axiom.s0();
    const string_exprt s1=nc_axiom.s1();

    symbol_exprt univ_var=generator.fresh_univ_index(
      "not_contains_univ_var", nc_axiom.s0().length().type());
    exprt wit=generator.get_witness_of(nc_axiom, univ_var);
    exprt val=get(wit);
    const string_not_contains_constraintt nc_axiom_in_model(
      get(univ_bound_inf),
      get(univ_bound_sup),
      get(prem),
      get(exists_bound_inf),
      get(exists_bound_sup),
      to_string_expr(get(s0)),
      to_string_expr(get(s1)));

    const exprt negaxiom=negation_of_not_contains_constraint(
      nc_axiom_in_model, val, univ_var);
    exprt witness;

    bool is_sat=is_axiom_sat(negaxiom, univ_var, witness);

    if(is_sat)
    {
      debug() << "string constraint can be violated for "
              << univ_var.get_identifier()
              << " = " << from_expr(ns, "", witness) << eom;
      violated_not_contains[i]=witness;
    }
  }

  if(violated.empty() && violated_not_contains.empty())
  {
    debug() << "no violated property" << eom;
    return true;
  }
  else
  {
    debug() << violated.size()
            << " universal string axioms can be violated" << eom;
    debug() << violated_not_contains.size()
            << " not_contains string axioms can be violated" << eom;

    if(use_counter_example)
    {
      // TODO: add counter examples for not_contains?

      // Checking if the current solution satisfies the constraints
      for(const auto &v : violated)
      {
        const exprt &val=v.second;
        const string_constraintt &axiom=universal_axioms[v.first];

        exprt premise(axiom.premise());
        exprt body(axiom.body());
        implies_exprt instance(premise, body);
        replace_expr(symbol_resolve, instance);
        replace_expr(axiom.univ_var(), val, instance);
        debug() << "adding counter example " << from_expr(ns, "", instance)
                << eom;
        add_lemma(instance);
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
      for(const auto &op : cur.operands())
        to_process.push_back(std::make_pair(op, positive));
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
  std::map<exprt, int> &m, const typet &type, bool negated) const
{
  exprt sum=nil_exprt();
  mp_integer constants=0;
  typet index_type;
  if(m.empty())
    return from_integer(0, type);
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
          if(sum.is_nil())
            sum=t;
          else
            plus_exprt(sum, t);
          for(int i=1; i<second; i++)
            sum=plus_exprt(sum, t);
        }
        else if(second<-1)
        {
          if(sum.is_nil())
            sum=unary_minus_exprt(t);
          else
            sum=minus_exprt(sum, t);
          for(int i=-1; i>second; i--)
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
  return sum_over_map(map, f.type());
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
  INVARIANT(
    it!=elems.end(),
    string_refinement_invariantt("a function must have an occurrence of qvar"));
  if(it->second==1 || it->second==-1)
  {
    neg=(it->second==1);
  }
  else
  {
    INVARIANT(
      it->second==0,
      string_refinement_invariantt("a proper function must have exactly one "
        "occurrences after reduction, or it canceled out, and it does not have "
        " one"));
    debug() << "in string_refinementt::compute_inverse_function:"
            << " warning: occurrences of qvar canceled out " << eom;
  }

  elems.erase(it);
  return sum_over_map(elems, f.type(), neg);
}



class find_qvar_visitort: public const_expr_visitort
{
private:
  const exprt &qvar_;

public:
  bool found;

  explicit find_qvar_visitort(const exprt &qvar): qvar_(qvar), found(false) {}

  void operator()(const exprt &expr) override
  {
    if(expr==qvar_)
      found=true;
  }
};

/// look for the symbol and return true if it is found
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

/// An expression representing an array of characters can be in the form of an
/// if expression for instance `cond?array1:(cond2:array2:array3)`.
/// We return all the array expressions contained in `array_expr`.
/// \param array_expr : an expression representing an array
/// \return a vector containing symbols and constant arrays contained in the
///         expression
static std::vector<exprt> sub_arrays(const exprt &array_expr)
{
  if(array_expr.id()==ID_if)
  {
    std::vector<exprt> res1=sub_arrays(to_if_expr(array_expr).true_case());
    std::vector<exprt> res2=sub_arrays(to_if_expr(array_expr).false_case());
    res1.insert(res1.end(), res2.begin(), res2.end());
    return res1;
  }
  else
  {
    INVARIANT(
      array_expr.id()==ID_symbol || array_expr.id()==ID_array,
      "character arrays should be symbol, constant array, or if expression");
    return std::vector<exprt>(1, array_expr);
  }
}

/// add to the index set all the indices that appear in the formula and the
/// upper bound minus one
/// \par parameters: a string constraint
void string_refinementt::add_to_index_set(const exprt &s, exprt i)
{
  simplify(i, ns);
  if(i.id()==ID_constant)
  {
    mp_integer mpi;
    to_integer(i, mpi);
    if(mpi<0)
      return;
  }

  std::vector<exprt> subs=sub_arrays(s);
  for(const auto &sub : subs)
    if(index_set[sub].insert(i).second)
      current_index_set[sub].insert(i);
}

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
        add_to_index_set(s, i);
      }
      else
      {
        // otherwise we add k-1
        exprt e(i);
        minus_exprt kminus1(
          axiom.upper_bound(),
          from_integer(1, axiom.upper_bound().type()));
        replace_expr(qvar, kminus1, e);
        add_to_index_set(s, e);
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
      DATA_INVARIANT(
        s.type().id()==ID_array,
        string_refinement_invariantt("index expressions must index on arrays"));
      exprt simplified=simplify_sum(i);
      add_to_index_set(s, simplified);
    }
    else
    {
      forall_operands(it, cur)
        to_process.push_back(*it);
    }
  }
}

// Will be used to visit an expression and return the index used
// with the given char array that contains qvar
class find_index_visitort: public const_expr_visitort
{
private:
  const exprt &str_;
  const symbol_exprt &qvar_;

public:
  exprt index;

  explicit find_index_visitort(
    const exprt &str, const symbol_exprt &qvar):
      str_(str),
      qvar_(qvar),
      index(nil_exprt()) {}

  void operator()(const exprt &expr) override
  {
    if(index.is_nil() && expr.id()==ID_index)
    {
      const index_exprt &i=to_index_expr(expr);
      if(i.array()==str_ && find_qvar(i.index(), qvar_))
        index=i.index();
    }
  }
};

/// Finds an index on `str` used in `expr` that contains `qvar`, for instance
/// with arguments ``(str[k] == 'a')``, `str`, and `k`, the function should
/// return `k`.
/// \param [in] expr: the expression to search
/// \param [in] str: the string which must be indexed
/// \param [in] qvar: the universal variable that must be in the index
/// \return an index expression in `expr` on `str` containing `qvar`
exprt find_index(const exprt &expr, const exprt &str, const symbol_exprt &qvar)
{
  find_index_visitort v(str, qvar);
  expr.visit(v);
  return v.index;
}

/// \par parameters: a universally quantified formula `axiom`, an array of char
/// variable `str`, and an index expression `val`.
/// \return substitute `qvar` the universally quantified variable of `axiom`, by
///   an index `val`, in `axiom`, so that the index used for `str` equals `val`.
///   For instance, if `axiom` corresponds to $\forall q. s[q+x]='a' &&
///   t[q]='b'$, `instantiate(axom,s,v)` would return an expression for
///   $s[v]='a' && t[v-x]='b'$.
exprt string_refinementt::instantiate(
  const string_constraintt &axiom, const exprt &str, const exprt &val)
{
  exprt idx=find_index(axiom.body(), str, axiom.univ_var());
  if(idx.is_nil())
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

/// instantiate a quantified formula representing `not_contains` by substituting
/// the quantifiers and generating axioms
/// \par parameters: a quantified formula representing `not_contains`, and a
/// list to which to add the created lemmas to
void string_refinementt::instantiate_not_contains(
  const string_not_contains_constraintt &axiom, std::list<exprt> &new_lemmas)
{
  exprt s0=axiom.s0();
  exprt s1=axiom.s1();

  debug() << "instantiate not contains " << from_expr(ns, "", s0) << " : "
          << from_expr(ns, "", s1) << eom;
  expr_sett index_set0=index_set[to_string_expr(s0).content()];
  expr_sett index_set1=index_set[to_string_expr(s1).content()];

  for(auto it0 : index_set0)
    for(auto it1 : index_set1)
    {
      debug() << from_expr(ns, "", it0) << " : " << from_expr(ns, "", it1)
              << eom;
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

/// replace array-lists by 'with' expressions
/// \par parameters: an expression containing array-list expressions
/// \return an epression containing no array-list
exprt string_refinementt::substitute_array_lists(exprt expr) const
{
  for(size_t i=0; i<expr.operands().size(); ++i)
  {
    // TODO: only copy when necessary
    exprt op(expr.operands()[i]);
    expr.operands()[i]=substitute_array_lists(op);
  }

  if(expr.id()=="array-list")
  {
    DATA_INVARIANT(
      expr.operands().size()>=2,
      string_refinement_invariantt("array-lists must have at least two "
        "operands"));
    typet &char_type=expr.operands()[1].type();
    array_typet arr_type(char_type, infinity_exprt(char_type));
    array_of_exprt new_arr(from_integer(0, char_type),
                           arr_type);

    with_exprt ret_expr(new_arr,
                        expr.operands()[0],
                        expr.operands()[1]);

    for(size_t i=1; i<expr.operands().size()/2; i++)
    {
      ret_expr=with_exprt(ret_expr,
                          expr.operands()[i*2],
                          expr.operands()[i*2+1]);
    }
    return ret_expr;
  }

  return expr;
}

/// evaluation of the expression in the current model
/// \par parameters: an expression
/// \return an expression
exprt string_refinementt::get(const exprt &expr) const
{
  exprt ecopy(expr);
  replace_expr(symbol_resolve, ecopy);
  if(is_char_array(ecopy.type()))
  {
    auto it_content=found_content.find(ecopy);
    if(it_content!=found_content.end())
      return it_content->second;

    auto it=found_length.find(ecopy);
    if(it!=found_length.end())
      return get_array(ecopy, it->second);
  }

  ecopy=supert::get(ecopy);

  return substitute_array_lists(ecopy);
}

/// Creates a solver with `axiom` as the only formula added and runs it. If it
/// is SAT, then true is returned and the given evalutation of `var` is stored
/// in `witness`. If UNSAT, then what witness is is undefined.
/// \param [in] axiom: the axiom to be checked
/// \param [in] var: the variable whose evaluation will be stored in witness
/// \param [out] witness: the witness of the satisfying assignment if one
///   exists. If UNSAT, then behaviour is undefined.
/// \return: true if axiom is SAT, false if UNSAT
bool string_refinementt::is_axiom_sat(
  const exprt &axiom, const symbol_exprt& var, exprt &witness)
{
  satcheck_no_simplifiert sat_check;
  supert solver(ns, sat_check);
  solver.set_ui(ui);
  solver << axiom;

  switch(solver())
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    {
      witness=solver.get(var);
      return true;
    }
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    return false;
  default:
    INVARIANT(false, string_refinement_invariantt("failure in checking axiom"));
    // To tell the compiler that the previous line bails
    throw 0;
  }
}

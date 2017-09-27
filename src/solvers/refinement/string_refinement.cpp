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

#include <iomanip>
#include <stack>
#include <util/expr_iterator.h>
#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/refinement/string_constraint_instantiation.h>
#include <java_bytecode/java_types.h>
#include "expr_cast.h"

static exprt substitute_array_with_expr(const exprt &expr, const exprt &index);

static bool is_char_array(const namespacet &ns, const typet &type);

static bool is_valid_string_constraint(
  messaget::mstreamt &stream,
  const namespacet &ns,
  const string_constraintt &expr);

static optionalt<exprt> find_counter_example(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const exprt &axiom,
  const symbol_exprt &var);

static std::pair<bool, std::vector<exprt>> check_axioms(
  const string_axiomst &axioms,
  string_constraint_generatort &generator,
  const std::function<exprt(const exprt &)> &get,
  messaget::mstreamt &stream,
  const namespacet &ns,
  std::size_t max_string_length,
  bool use_counter_example,
  ui_message_handlert::uit ui,
  const replace_mapt &symbol_resolve);

static void initial_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const string_constraintt &axiom);

static void initial_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const string_not_contains_constraintt &axiom);

static void initial_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const string_axiomst &axioms);

exprt simplify_sum(const exprt &f);

static void update_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const std::vector<exprt> &current_constraints);

static void update_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const exprt &formula);

static exprt instantiate(
  messaget::mstreamt &stream,
  const string_constraintt &axiom,
  const exprt &str,
  const exprt &val);

static std::vector<exprt> instantiate(
  const string_not_contains_constraintt &axiom,
  const index_set_pairt &index_set,
  const string_constraint_generatort &generator);

static exprt get_array(
  const std::function<exprt(const exprt &)> &super_get,
  const exprt &arr);

/// Convert index-value map to a vector of values. If a value for an
/// index is not defined, set it to the value referenced by the next higher
/// index. The length of the resulting vector is the key of the map's
/// last element + 1
/// \param index_value: map containing values of specific vector cells
/// \return Vector containing values as described in the map
template <typename T>
static std::vector<T> fill_in_map_as_vector(
  const std::map<std::size_t, T> &index_value)
{
  std::vector<T> result;
  if(!index_value.empty())
  {
    result.resize(index_value.rbegin()->first+1);
    for(auto it=index_value.rbegin(); it!=index_value.rend(); ++it)
    {
      const std::size_t index=it->first;
      const T& value=it->second;
      const auto next=std::next(it);
      const std::size_t leftmost_index_to_pad=
        next!=index_value.rend()
        ? next->first+1
        : 0;
      for(std::size_t j=leftmost_index_to_pad; j<=index; j++)
        result[j]=value;
    }
  }
  return result;
}


static bool validate(const string_refinementt::infot &info)
{
  PRECONDITION(info.ns);
  PRECONDITION(info.prop);
  return true;
}

string_refinementt::string_refinementt(const infot &info, bool):
  supert(info),
  config_(info),
  loop_bound_(info.refinement_bound),
  generator(info, *info.ns) { }

string_refinementt::string_refinementt(const infot &info):
  string_refinementt(info, validate(info)) { }

/// display the current index set, for debugging
static void display_index_set(
  messaget::mstreamt stream,
  const namespacet &ns,
  const index_set_pairt &index_set)
{
  const auto eom=messaget::eom;
  std::size_t count=0;
  std::size_t count_current=0;
  for(const auto &i : index_set.cumulative)
  {
    const exprt &s=i.first;
    stream << "IS(" << from_expr(ns, "", s) << ")=={" << eom;

    for(const auto &j : i.second)
    {
      const auto it=index_set.current.find(i.first);
      if(it!=index_set.current.end() && it->second.find(j)!=it->second.end())
      {
        count_current++;
        stream << "**";
      }
      stream << "  " << from_expr(ns, "", j) << ";" << eom;
      count++;
    }
    stream << "}"  << eom;
  }
  stream << count << " elements in index set (" << count_current
         << " newly added)" << eom;
}

static std::vector<exprt> generate_instantiations(
  messaget::mstreamt &stream,
  const namespacet &ns,
  const string_constraint_generatort &generator,
  const index_set_pairt &index_set,
  const string_axiomst &axioms)
{
  std::vector<exprt> lemmas;
  for(const auto &i : index_set.current)
  {
    for(const auto &univ_axiom : axioms.universal)
    {
      for(const auto &j : i.second)
        lemmas.push_back(instantiate(stream, univ_axiom, i.first, j));
    }
  }
  for(const auto &nc_axiom : axioms.not_contains)
  {
    for(const auto &instance :
      instantiate(nc_axiom, index_set, generator))
      lemmas.push_back(instance);
  }
  return lemmas;
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
void add_symbol_to_symbol_map(
  replace_mapt &symbol_resolve,
  std::map<exprt, std::list<exprt>> &reverse_symbol_resolve,
  const exprt &lhs,
  const exprt &rhs)
{
  PRECONDITION(lhs.id()==ID_symbol);
  PRECONDITION(rhs.id()==ID_symbol ||
               rhs.id()==ID_array ||
               rhs.id()==ID_array_of ||
               rhs.id()==ID_if ||
               (rhs.id()==ID_struct &&
                is_refined_string_type(rhs.type())));

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
std::vector<exprt> set_char_array_equality(const exprt &lhs, const exprt &rhs)
{
  PRECONDITION(lhs.id()==ID_symbol);

  if(rhs.id()==ID_array && rhs.type().id()==ID_array)
  {
    std::vector<exprt> lemmas;
    const typet &index_type=to_array_type(rhs.type()).size().type();
    for(size_t i=0, ilim=rhs.operands().size(); i!=ilim; ++i)
    {
      // Introduce axioms to map symbolic rhs to its char array.
      index_exprt arraycell(rhs, from_integer(i, index_type));
      equal_exprt arrayeq(arraycell, rhs.operands()[i]);
      lemmas.push_back(arrayeq);
    }
    return lemmas;
  }
  return { };
  // At least for Java (as it is currently pre-processed), we need not consider
  // other cases, because all character arrays find themselves on the rhs of an
  // equality. Note that this might not be the case for other languages.
}

/// distinguish char array from other types
///
/// TODO: this is only for java char array and does not work for other languages
/// \param type: a type
/// \return true if the given type is an array of java characters
static bool is_char_array(const namespacet &ns, const typet &type)
{
  if(type.id()==ID_symbol)
    return is_char_array(ns, ns.follow(type));

  return (type.id()==ID_array && type.subtype()==java_char_type());
}

/// add lemmas to the solver corresponding to the given equation
/// \param lhs: left hand side of an equality expression
/// \param rhs: right and side of the equality
/// \return true if the assignemnt needs to be handled by the parent class
///         via `set_to`
std::pair<bool, std::vector<exprt>> add_axioms_for_string_assigns(
  replace_mapt &symbol_resolve,
  std::map<exprt, std::list<exprt>> &reverse_symbol_resolve,
  string_constraint_generatort &generator,
  messaget::mstreamt &stream,
  const namespacet &ns,
  const exprt &lhs,
  const exprt &rhs)
{
  if(is_char_array(ns, rhs.type()))
  {
    std::vector<exprt> lemmas=set_char_array_equality(lhs, rhs);
    if(rhs.id()==ID_symbol || rhs.id()==ID_array)
    {
      add_symbol_to_symbol_map(
        symbol_resolve,
        reverse_symbol_resolve,
        lhs,
        rhs);
      return { false, std::move(lemmas) };
    }
    else if(rhs.id()==ID_nondet_symbol)
    {
      add_symbol_to_symbol_map(
        symbol_resolve,
        reverse_symbol_resolve,
        lhs,
        generator.fresh_symbol("nondet_array", lhs.type()));
      return { false, std::move(lemmas) };
    }
    else if(rhs.id()==ID_if)
    {
      add_symbol_to_symbol_map(
        symbol_resolve,
        reverse_symbol_resolve,
        lhs,
        rhs);
      return { true, std::move(lemmas) };
    }
    else
    {
      stream << "ignoring char array " << from_expr(ns, "", rhs)
             << messaget::eom;
      return { true, std::move(lemmas) };
    }
  }
  if(is_refined_string_type(rhs.type()))
  {
    exprt refined_rhs=generator.add_axioms_for_refined_string(rhs);
    add_symbol_to_symbol_map(
      symbol_resolve,
      reverse_symbol_resolve,
      lhs,
      refined_rhs);
    return { false, std::vector<exprt>() };
  }
  // Other cases are to be handled by supert::set_to.
  return { true, std::vector<exprt>() };
}

/// For each string whose length has been solved, add constants to the map
/// `found_length`
void concretize_lengths(
  std::map<exprt, exprt> &found_length,
  const std::function<exprt(const exprt &)> &get,
  const replace_mapt &symbol_resolve,
  const std::set<string_exprt> &created_strings)
{
  for(const auto &pair : symbol_resolve)
  {
    if(const auto str=expr_cast<string_exprt>(pair.second))
    {
      exprt length=get(str->length());
      exprt content=str->content();
      replace_expr(symbol_resolve, content);
      found_length[content]=length;
    }
  }
  for(const auto &it : created_strings)
  {
    if(const auto str=expr_cast<string_exprt>(it))
    {
      exprt length=get(str->length());
      exprt content=str->content();
      replace_expr(symbol_resolve, content);
      found_length[content]=length;
     }
  }
}

/// add lemmas representing the setting of an expression to a given value
/// \par parameters: an expression and the value to set it to
void string_refinementt::set_to(const exprt &expr, bool value)
{
  PRECONDITION(expr.type().id()==ID_bool);
  PRECONDITION(equality_propagation);

  if(expr.id()==ID_equal)
  {
    equal_exprt eq_expr=to_equal_expr(expr);
    const exprt &lhs=eq_expr.lhs();
    const exprt &rhs=eq_expr.rhs();

    // The assignment of a string equality to false is not supported.
    PRECONDITION(value || !is_char_array(ns, rhs.type()));
    PRECONDITION(value || !is_refined_string_type(rhs.type()));

    PRECONDITION(lhs.id()==ID_symbol || !is_char_array(ns, rhs.type()));
    PRECONDITION(lhs.id()==ID_symbol || !is_refined_string_type(rhs.type()));

    // If lhs is not a symbol, let supert::set_to() handle it.
    if(lhs.id()!=ID_symbol)
    {
      non_string_axioms.emplace_back(expr, value);
      return;
    }

    if(lhs.type()!=rhs.type())
    {
      warning() << "ignoring " << from_expr(ns, "", expr)
                << " [inconsistent types]" << eom;
      debug() << "lhs has type: " << lhs.type().pretty(12) << eom;
      debug() << "rhs has type: " << rhs.type().pretty(12) << eom;
      return;
    }

    // Preprocessing to remove function applications.
    debug() << "(sr::set_to) " << from_expr(ns, "", lhs)
            << "=" << from_expr(ns, "", rhs) << eom;

    const exprt subst_rhs=generator.substitute_function_applications(rhs);
    if(lhs.type()!=subst_rhs.type())
    {
      if(lhs.type().id()!=ID_array ||
         subst_rhs.type().id()!=ID_array ||
         lhs.type().subtype()!=subst_rhs.type().subtype())
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
      bool not_handled;
      std::vector<exprt> lemmas;
      std::tie(not_handled, lemmas)=add_axioms_for_string_assigns(
        symbol_resolve,
        reverse_symbol_resolve,
        generator,
        warning(),
        ns,
        lhs,
        subst_rhs);
      for(const auto &lemma : lemmas)
        add_lemma(lemma, false);
      if(!not_handled)
        return;
    }

    // Push the substituted equality to the list of axioms to be given to
    // supert::set_to.
    non_string_axioms.emplace_back(equal_exprt(lhs, subst_rhs), value);
  }
  // Push the unmodified equality to the list of axioms to be given to
  // supert::set_to.
  else
  {
    // TODO: Verify that the expression contains no string.
    // This will be easy once exprt iterators will have been implemented.
    non_string_axioms.emplace_back(expr, value);
  }
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

  for(string_constraintt constraint : generator.constraints())
  {
    replace_expr(symbol_resolve, constraint);
    DATA_INVARIANT(
      is_valid_string_constraint(debug(), ns, constraint),
      string_refinement_invariantt(
        "string constraints satisfy their invariant"));
    axioms.universal.push_back(constraint);
  }

  for(auto nc_axiom : generator.not_contains_constraints())
  {
    replace_expr(symbol_resolve, nc_axiom);
    const refined_string_typet rtype=to_refined_string_type(nc_axiom.s0().type());
    const typet &index_type=rtype.get_index_type();
    const array_typet witness_type(index_type, infinity_exprt(index_type));
    generator.witness[nc_axiom]=
      generator.fresh_symbol("not_contains_witness", witness_type);
    axioms.not_contains.push_back(nc_axiom);
  }
  for(exprt lemma : generator.lemmas())
  {
    replace_expr(symbol_resolve, lemma);
    add_lemma(lemma);
  }

  found_length.clear();
  found_content.clear();

  const auto get=[this](const exprt &expr) { return this->get(expr); };

  // Initial try without index set
  const decision_proceduret::resultt res=supert::dec_solve();
  if(res==resultt::D_SATISFIABLE)
  {
    bool satisfied;
    std::vector<exprt> counter_examples;
    std::tie(satisfied, counter_examples)=check_axioms(
      axioms,
      generator,
      get,
      debug(),
      ns,
      generator.max_string_length,
      config_.use_counter_example,
      supert::config_.ui,
      symbol_resolve);
    if(!satisfied)
    {
      for(const auto &counter : counter_examples)
        add_lemma(counter);
      debug() << "check_SAT: got SAT but the model is not correct" << eom;
    }
    else
    {
      debug() << "check_SAT: the model is correct" << eom;
      concretize_lengths(
        found_length,
        get,
        symbol_resolve,
        generator.get_created_strings());
      return resultt::D_SATISFIABLE;
    }
  }
  else
  {
    debug() << "check_SAT: got UNSAT or ERROR" << eom;
    return res;
  }

  initial_index_set(index_sets, ns, axioms);
  update_index_set(index_sets, ns, current_constraints);
  display_index_set(debug(), ns, index_sets);
  current_constraints.clear();
  for(const auto &instance :
        generate_instantiations(
          debug(),
          ns,
          generator,
          index_sets,
          axioms))
    add_lemma(instance);

  while((loop_bound_--)>0)
  {
    const decision_proceduret::resultt res=supert::dec_solve();

    if(res==resultt::D_SATISFIABLE)
    {
      bool satisfied;
      std::vector<exprt> counter_examples;
      std::tie(satisfied, counter_examples)=check_axioms(
        axioms,
        generator,
        get,
        debug(),
        ns,
        generator.max_string_length,
        config_.use_counter_example,
        supert::config_.ui,
        symbol_resolve);
      if(!satisfied)
      {
        for(const auto &counter : counter_examples)
          add_lemma(counter);
        debug() << "check_SAT: got SAT but the model is not correct" << eom;
      }
      else
      {
        debug() << "check_SAT: the model is correct" << eom;
        concretize_lengths(
          found_length,
          get,
          symbol_resolve,
          generator.get_created_strings());
        return resultt::D_SATISFIABLE;
      }

      debug() <<  "refining..." << eom;
      // Since the model is not correct although we got SAT, we need to refine
      // the property we are checking by adding more indices to the index set,
      // and instantiating universal formulas with this indices.
      // We will then relaunch the solver with these added lemmas.
      index_sets.current.clear();
      update_index_set(index_sets, ns, current_constraints);

      if(index_sets.current.empty())
      {
        debug() << "current index set is empty" << eom;
        if(axioms.not_contains.empty())
        {
          debug() << "no not_contains axioms, hence SAT" << eom;
          concretize_lengths(
            found_length,
            get,
            symbol_resolve,
            generator.get_created_strings());
          return resultt::D_SATISFIABLE;
        }
        else
        {
          debug() << "not_contains axioms exist, hence ERROR" << eom;
          return resultt::D_ERROR;
        }
      }

      display_index_set(debug(), ns, index_sets);
      current_constraints.clear();
      for(const auto &instance :
        generate_instantiations(
          debug(),
          ns,
          generator,
          index_sets,
          axioms))
        add_lemma(instance);
    }
    else
    {
      debug() << "check_SAT: default return " << static_cast<int>(res) << eom;
      return res;
    }
  }
  debug() << "string_refinementt::dec_solve reached the maximum number"
           << "of steps allowed" << eom;
  return resultt::D_ERROR;
}

/// add the given lemma to the solver
/// \par parameters: a lemma and Boolean value stating whether the lemma should
/// be added to the index set.
void string_refinementt::add_lemma(
  const exprt &lemma, const bool _simplify)
{
  if(!seen_instances.insert(lemma).second)
    return;

  current_constraints.push_back(lemma);

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
static exprt get_array(
  const std::function<exprt(const exprt &)> &super_get,
  const namespacet &ns,
  const std::size_t max_string_length,
  const exprt &arr,
  const exprt &size)
{
  exprt arr_val=simplify_expr(get_array(super_get, arr), ns);
  exprt size_val=super_get(size);
  size_val=simplify_expr(size_val, ns);
  typet char_type=arr.type().subtype();
  const typet &index_type=size.type();
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

  if(n>max_string_length)
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

  if(arr_val.id()=="array-list")
  {
    DATA_INVARIANT(
      arr_val.operands().size()%2==0,
      string_refinement_invariantt("and index expression must be on a symbol, "
                                   "with, array_of, if, or array, and all "
                                   "cases besides array are handled above"));
    std::map<std::size_t, exprt> initial_map;
    for(size_t i=0; i<arr_val.operands().size()/2; i++)
    {
      exprt index=arr_val.operands()[i*2];
      unsigned idx;
      if(!to_unsigned_integer(to_constant_expr(index), idx) && idx<n)
        initial_map[idx]=arr_val.operands()[i*2+1];
    }

    // Pad the concretized values to the left to assign the uninitialized
    // values of result.
    ret.operands()=fill_in_map_as_vector(initial_map);
    return ret;
  }
  else if(arr_val.id()==ID_array)
  {
    // copy the `n` first elements of `arr_val`
    for(size_t i=0; i<arr_val.operands().size() && i<n; i++)
      ret.move_to_operands(arr_val.operands()[i]);
    return ret;
  }
  // default return value is an array of `0`s
  return array_of_exprt(from_integer(0, char_type), ret_type);
}

/// get a model of an array of unknown size and infer the size if possible
/// \par parameters: an expression representing an array
/// \return an expression
static exprt get_array(
  const std::function<exprt(const exprt &)> &super_get,
  const exprt &arr)
{
  exprt arr_model=super_get(arr);
  if(arr_model.id()==ID_array)
  {
    array_typet &arr_type=to_array_type(arr_model.type());
    arr_type.size()=from_integer(
      arr_model.operands().size(), arr_type.size().type());
  }
  return arr_model;
}

/// convert the content of a string to a more readable representation. This
/// should only be used for debugging.
/// \par parameters: a constant array expression and a integer expression
/// \return a string
static std::string string_of_array(const array_exprt &arr)
{
  unsigned n;
  if(arr.type().id()!=ID_array)
      return std::string("");

  exprt size_expr=to_array_type(arr.type()).size();
  PRECONDITION(size_expr.id()==ID_constant);
  to_unsigned_integer(to_constant_expr(size_expr), n);
  return utf16_constant_array_to_java(arr, n);
}

/// Display part of the current model by mapping the variables created by the
/// solver to constant expressions given by the current model
void debug_model(
  const replace_mapt &symbol_resolve,
  messaget::mstreamt &stream,
  const namespacet &ns,
  const std::size_t max_string_length,
  const std::function<exprt(const exprt &)> &super_get,
  const std::vector<symbol_exprt> &boolean_symbols,
  const std::vector<symbol_exprt> &index_symbols)
{
  const std::string indent("  ");
  for(auto it : symbol_resolve)
  {
    if(const auto refined=expr_cast<string_exprt>(it.second))
    {
      stream << "- " << from_expr(ns, "", to_symbol_expr(it.first)) << ":\n"
             << indent << indent << "in_map: "
             << from_expr(ns, "", *refined) << '\n'
             << indent << indent << "resolved: "
             << from_expr(ns, "", *refined) << '\n';
      const exprt &econtent=refined->content();
      const exprt &elength=refined->length();

      exprt len=super_get(elength);
      len=simplify_expr(len, ns);
      const exprt arr=get_array(
        super_get,
        ns,
        max_string_length,
        econtent, len);
      if(arr.id()==ID_array)
        stream << indent << indent << "as_string: \""
               << string_of_array(to_array_expr(arr)) << "\"\n";
      else
        stream << indent << indent << "as_char_array: "
               << from_expr(ns, "", arr) << "\n";

      stream << indent << indent << "size: " << from_expr(ns, "", len) << '\n';
    }
    else
    {
      INVARIANT(
        is_char_array(ns, it.second.type()),
        string_refinement_invariantt("symbol_resolve should only map to "
          "refined_strings or to char_arrays, and refined_strings are already "
          "handled"));
      exprt arr=it.second;
      replace_expr(symbol_resolve, arr);
      stream << "- " << from_expr(ns, "", to_symbol_expr(it.first)) << ":\n";
      stream << indent << indent << "resolved: "
              << from_expr(ns, "", arr) << "\n";
      exprt arr_model=get_array(super_get, arr);
      stream << indent << indent << "char_array: "
             << from_expr(ns, "", arr_model) << '\n';
    }
  }

  for(const auto &it : boolean_symbols)
  {
      stream << " - " << it.get_identifier() << ": "
             << from_expr(ns, "", super_get(it)) << '\n';
  }

  for(const auto &it : index_symbols)
  {
     stream << " - " << it.get_identifier() << ": "
            << from_expr(ns, "", super_get(it)) << '\n';
  }
  stream << messaget::eom;
}

/// Create a new expression where 'with' expressions on arrays are replaced by
/// 'if' expressions. e.g. for an array access arr[x], where: `arr :=
/// array_of(12) with {0:=24} with {2:=42}` the constructed expression will be:
/// `index==0 ? 24 : index==2 ? 42 : 12`
/// \param expr: A (possibly nested) 'with' expression on an `array_of`
///   expression
/// \param index: An index with which to build the equality condition
/// \return An expression containing no 'with' expression
static exprt substitute_array_with_expr(const exprt &expr, const exprt &index)
{
  if(expr.id()==ID_with)
  {
    const with_exprt &with_expr=to_with_expr(expr);
    const exprt &then_expr=with_expr.new_value();
    exprt else_expr=substitute_array_with_expr(with_expr.old(), index);
    const typet &type=then_expr.type();
    CHECK_RETURN(else_expr.type()==type);
    CHECK_RETURN(index.type()==with_expr.where().type());
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

/// Fill an array represented by a list of with_expr by propagating values to
/// the left. For instance `ARRAY_OF(12) WITH[2:=24] WITH[4:=42]` will give
/// `{ 24, 24, 24, 42, 42 }`
/// \param expr: an array expression in the form
///   `ARRAY_OF(x) WITH [i0:=v0] ... WITH [iN:=vN]`
/// \param string_max_length: bound on the length of strings
/// \return an array expression with filled in values, or expr if it is simply
///   an `ARRAY_OF(x)` expression
exprt fill_in_array_with_expr(
  const exprt &expr,
  const std::size_t string_max_length)
{
  PRECONDITION(expr.type().id()==ID_array);
  PRECONDITION(expr.id()==ID_with || expr.id()==ID_array_of);

  // Nothing to do for empty array
  if(expr.id()==ID_array_of)
    return expr;

  // Map of the parts of the array that are initialized
  std::map<std::size_t, exprt> initial_map;

  for(exprt it=expr; it.id()==ID_with; it=to_with_expr(it).old())
  {
    // Add to `initial_map` all the pairs (index,value) contained in `WITH`
    // statements
    const with_exprt with_expr=to_with_expr(it);
    const exprt &then_expr=with_expr.new_value();
    const auto index=expr_cast_v<std::size_t>(with_expr.where());
    if(index<string_max_length)
      initial_map.emplace(index, then_expr);
  }

  array_exprt result(to_array_type(expr.type()));
  result.operands()=fill_in_map_as_vector(initial_map);
  return result;
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
static void substitute_array_access(exprt &expr)
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
      expr=substitute_array_with_expr(index_expr.array(), index_expr.index());
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

    // Empty arrays do not need to be substituted.
    if(array_expr.operands().empty())
      return;

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
/// an assignment of the universal variable that would violate the axiom. To
/// avoid false positives, the symbols other than the universal variable should
/// have been replaced by their valuation in the current model.
/// \pre Symbols other than the universal variable should have been replaced by
///   their valuation in the current model.
/// \param axiom: the not_contains constraint to add the negation of
/// \param univ_var: the universal variable for the negation of the axiom
/// \return: the negation of the axiom under the current evaluation
static exprt negation_of_not_contains_constraint(
  const string_not_contains_constraintt &axiom,
  const symbol_exprt &univ_var)
{
  // If the for all is vacuously true, the negation is false.
  const exprt &lbu=axiom.univ_lower_bound();
  const exprt &ubu=axiom.univ_upper_bound();
  if(lbu.id()==ID_constant && ubu.id()==ID_constant)
  {
    const auto lb_int=expr_cast<mp_integer>(lbu);
    const auto ub_int=expr_cast<mp_integer>(ubu);
    if(!lb_int || !ub_int || *ub_int<=*lb_int)
      return false_exprt();
  }

  const auto lbe=expr_cast_v<mp_integer>(axiom.exists_lower_bound());
  const auto ube=expr_cast_v<mp_integer>(axiom.exists_upper_bound());

  // If the premise is false, the implication is trivially true, so the
  // negation is false.
  if(axiom.premise()==false_exprt())
    return false_exprt();

  and_exprt univ_bounds(
    binary_relation_exprt(lbu, ID_le, univ_var),
    binary_relation_exprt(ubu, ID_gt, univ_var));

  // The negated existential becomes an universal, and this is the unrolling of
  // that universal quantifier.
  std::vector<exprt> conjuncts;
  for(mp_integer i=lbe; i<ube; ++i)
  {
    const constant_exprt i_exprt=from_integer(i, univ_var.type());
    const equal_exprt equal_chars(
      axiom.s0()[plus_exprt(univ_var, i_exprt)],
      axiom.s1()[i_exprt]);
    conjuncts.push_back(equal_chars);
  }
  exprt equal_strings=conjunction(conjuncts);
  and_exprt negaxiom(univ_bounds, axiom.premise(), equal_strings);

  return negaxiom;
}

/// Negates the constraint to be fed to a solver. The intended usage is to find
/// an assignment of the universal variable that would violate the axiom. To
/// avoid false positives, the symbols other than the universal variable should
/// have been replaced by their valuation in the current model.
/// \pre Symbols other than the universal variable should have been replaced by
///   their valuation in the current model.
/// \param axiom: the not_contains constraint to add the negation of
/// \return: the negation of the axiom under the current evaluation
static exprt negation_of_constraint(const string_constraintt &axiom)
{
  // If the for all is vacuously true, the negation is false.
  const exprt &lb=axiom.lower_bound();
  const exprt &ub=axiom.upper_bound();
  if(lb.id()==ID_constant && ub.id()==ID_constant)
  {
    const auto lb_int=expr_cast<mp_integer>(lb);
    const auto ub_int=expr_cast<mp_integer>(ub);
    if(!lb_int || !ub_int || ub_int<=lb_int)
      return false_exprt();
  }

  // If the premise is false, the implication is trivially true, so the
  // negation is false.
  if(axiom.premise()==false_exprt())
    return false_exprt();

  and_exprt premise(axiom.premise(), axiom.univ_within_bounds());
  and_exprt negaxiom(premise, not_exprt(axiom.body()));

  return negaxiom;
}

/// Result of the solver `supert` should not be interpreted literally for char
/// arrays as not all indices are present in the index set.
/// In the given expression, we populate arrays at the indices for which the
/// solver has no constraint by copying values to the left.
/// For example an expression `ARRAY_OF(0) WITH [1:=2] WITH [4:=3]` would
/// be interpreted as `{ 2, 2, 3, 3, 3}`.
/// \param expr: expression to interpret
/// \param string_max_length: maximum size of arrays to consider
/// \return the interpreted expression
exprt concretize_arrays_in_expression(exprt expr, std::size_t string_max_length)
{
  auto it=expr.depth_begin();
  const auto end=expr.depth_end();
  while(it!=end)
  {
    if(it->id()==ID_with && it->type().id()==ID_array)
    {
      it.mutate()=fill_in_array_with_expr(*it, string_max_length);
      it.next_sibling_or_parent();
    }
    else
      ++it;
  }
  return expr;
}

/// return true if the current model satisfies all the axioms
/// \return a Boolean
static std::pair<bool, std::vector<exprt>> check_axioms(
  const string_axiomst &axioms,
  string_constraint_generatort &generator,
  const std::function<exprt(const exprt &)> &get,
  messaget::mstreamt &stream,
  const namespacet &ns,
  std::size_t max_string_length,
  bool use_counter_example,
  ui_message_handlert::uit ui,
  const replace_mapt &symbol_resolve)
{
  const auto eom=messaget::eom;
  stream << "string_refinementt::check_axioms:" << eom;

  #if 0
  debug_model(symbol_resolve,
    stream,
    ns,
    max_string_length,
    get,
    generator.get_boolean_symbols(),
    generator.get_index_symbols());
  #endif

  // Maps from indexes of violated universal axiom to a witness of violation
  std::map<size_t, exprt> violated;

  stream << "string_refinement::check_axioms: " << axioms.universal.size()
         << " universal axioms:" << eom;
  for(size_t i=0; i<axioms.universal.size(); i++)
  {
    const string_constraintt &axiom=axioms.universal[i];
    const symbol_exprt &univ_var=axiom.univ_var();
    const exprt &bound_inf=axiom.lower_bound();
    const exprt &bound_sup=axiom.upper_bound();
    const exprt &prem=axiom.premise();
    const exprt &body=axiom.body();

    const string_constraintt axiom_in_model(
      univ_var, get(bound_inf), get(bound_sup), get(prem), get(body));

    exprt negaxiom=negation_of_constraint(axiom_in_model);

    stream << "  " << i << ".\n"
           << "    - axiom:\n"
           << "       " << from_expr(ns, "", axiom) << '\n';
    stream << "    - axiom_in_model:\n"
           << "       " << from_expr(ns, "", axiom_in_model) << '\n';
    stream << "    - negated_axiom:\n"
           << "       " << from_expr(ns, "", negaxiom) << '\n';

    exprt with_concretized_arrays=concretize_arrays_in_expression(
      negaxiom, max_string_length);
    stream << "    - negated_axiom_with_concretized_array_access:\n"
           << "       " << from_expr(ns, "", with_concretized_arrays) << '\n';

    substitute_array_access(with_concretized_arrays);
    stream << "    - negated_axiom_without_array_access:\n"
           << "       " << from_expr(ns, "", with_concretized_arrays) << '\n';

    if(const auto &witness=
       find_counter_example(ns, ui, with_concretized_arrays, univ_var))
    {
      stream << "  - violated_for: "
             << univ_var.get_identifier()
             << "=" << from_expr(ns, "", *witness) << '\n';
      violated[i]=*witness;
    }
    else
      stream << "  - correct" << '\n';
  }

  // Maps from indexes of violated not_contains axiom to a witness of violation
  std::map<std::size_t, exprt> violated_not_contains;

  stream << "there are " << axioms.not_contains.size()
         << " not_contains axioms" << eom;
  for(size_t i=0; i<axioms.not_contains.size(); i++)
  {
    const string_not_contains_constraintt &nc_axiom=axioms.not_contains[i];
    const exprt &univ_bound_inf=nc_axiom.univ_lower_bound();
    const exprt &univ_bound_sup=nc_axiom.univ_upper_bound();
    const exprt &prem=nc_axiom.premise();
    const exprt &exists_bound_inf=nc_axiom.exists_lower_bound();
    const exprt &exists_bound_sup=nc_axiom.exists_upper_bound();
    const string_exprt &s0=nc_axiom.s0();
    const string_exprt &s1=nc_axiom.s1();

    symbol_exprt univ_var=generator.fresh_univ_index(
      "not_contains_univ_var", nc_axiom.s0().length().type());
    const string_not_contains_constraintt nc_axiom_in_model(
      get(univ_bound_inf),
      get(univ_bound_sup),
      get(prem),
      get(exists_bound_inf),
      get(exists_bound_sup),
      to_string_expr(get(s0)),
      to_string_expr(get(s1)));

    exprt negaxiom=negation_of_not_contains_constraint(
      nc_axiom_in_model, univ_var);

    stream << "  " << i << ".\n"
           << "    - axiom:\n"
           << "       " << from_expr(ns, "", nc_axiom) << '\n';
    stream << "    - axiom_in_model:\n"
           << "       " << from_expr(ns, "", nc_axiom_in_model) << '\n';
    stream << "    - negated_axiom:\n"
           << "       " << from_expr(ns, "", negaxiom) << '\n';

    exprt with_concretized_arrays=concretize_arrays_in_expression(
      negaxiom, max_string_length);
    stream << "    - negated_axiom_with_concretized_array_access:\n"
           << "       " << from_expr(ns, "", with_concretized_arrays) << '\n';

    substitute_array_access(with_concretized_arrays);
    stream << "    - negated_axiom_without_array_access:\n"
           << "       " << from_expr(ns, "", with_concretized_arrays) << '\n';

    if(const auto &witness=
      find_counter_example(ns, ui, with_concretized_arrays, univ_var))
    {
      stream << "  - violated_for: "
             << univ_var.get_identifier()
             << "=" << from_expr(ns, "", *witness) << '\n';
      violated_not_contains[i]=*witness;
    }
    else
      stream << "  - correct" << '\n';
  }

  if(violated.empty() && violated_not_contains.empty())
  {
    stream << "no violated property" << eom;
    return { true, std::vector<exprt>() };
  }
  else
  {
    stream << violated.size()
           << " universal string axioms can be violated" << eom;
    stream << violated_not_contains.size()
           << " not_contains string axioms can be violated" << eom;

    if(use_counter_example)
    {
      stream << "Adding counter-examples: " << eom;

      std::vector<exprt> lemmas;

      for(const auto &v : violated)
      {
        const exprt &val=v.second;
        const string_constraintt &axiom=axioms.universal[v.first];

        implies_exprt instance(axiom.premise(), axiom.body());
        replace_expr(axiom.univ_var(), val, instance);
        // We are not sure the index set contains only positive numbers
        exprt bounds=and_exprt(
          axiom.univ_within_bounds(),
          binary_relation_exprt(
            from_integer(0, val.type()), ID_le, val));
        replace_expr(axiom.univ_var(), val, bounds);
        const implies_exprt counter(bounds, instance);

        stream << "  -  " << from_expr(ns, "", counter) << eom;
        lemmas.push_back(counter);
      }

      for(const auto &v : violated_not_contains)
      {
        const exprt &val=v.second;
        const string_not_contains_constraintt &axiom=
          axioms.not_contains[v.first];

        const exprt func_val=generator.get_witness_of(axiom, val);
        const exprt comp_val=simplify_sum(plus_exprt(val, func_val));

        std::set<std::pair<exprt, exprt>> indices;
        indices.insert(std::pair<exprt, exprt>(comp_val, func_val));
        const exprt counter=::instantiate_not_contains(
          axiom, indices, generator)[0];

        stream << "  -  " << from_expr(ns, "", counter) << eom;
        lemmas.push_back(counter);
      }
      return { false, lemmas };
    }
  }
  return { false, std::vector<exprt>() };
}

/// \par parameters: an expression with only addition and subtraction
/// \return a map where each leaf of the input is mapped to the number of times
///   it is added. For instance, expression $x + x - y$ would give the map x ->
///   2, y -> -1.
static std::map<exprt, int> map_representation_of_sum(const exprt &f)
{
  // number of time the leaf should be added (can be negative)
  std::map<exprt, int> elems;

  std::list<std::pair<exprt, bool> > to_process;
  to_process.emplace_back(f, true);

  while(!to_process.empty())
  {
    exprt cur=to_process.back().first;
    bool positive=to_process.back().second;
    to_process.pop_back();
    if(cur.id()==ID_plus)
    {
      for(const auto &op : cur.operands())
        to_process.emplace_back(op, positive);
    }
    else if(cur.id()==ID_minus)
    {
      to_process.emplace_back(cur.op1(), !positive);
      to_process.emplace_back(cur.op0(), positive);
    }
    else if(cur.id()==ID_unary_minus)
    {
      to_process.emplace_back(cur.op0(), !positive);
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
static exprt sum_over_map(
  std::map<exprt, int> &m,
  const typet &type,
  bool negated=false)
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
/// \return an equivalent expression in a canonical form
exprt simplify_sum(const exprt &f)
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
static exprt compute_inverse_function(
  messaget::mstreamt &stream,
  const exprt &qvar,
  const exprt &val,
  const exprt &f)
{
  exprt positive, negative;
  // number of time the element should be added (can be negative)
  // qvar has to be equal to val - f(0) if it appears positively in f
  // (i.e. if f(qvar)=f(0) + qvar) and f(0) - val if it appears negatively
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
    stream << "in string_refinementt::compute_inverse_function:"
           << " warning: occurrences of qvar canceled out " << messaget::eom;
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
static bool find_qvar(const exprt &index, const symbol_exprt &qvar)
{
  find_qvar_visitort v2(qvar);
  index.visit(v2);
  return v2.found;
}

/// add to the index set all the indices that appear in the formulas and the
/// upper bound minus one
/// \par parameters: a list of string constraints
static void initial_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const string_axiomst &axioms)
{
  for(const auto &axiom : axioms.universal)
    initial_index_set(index_set, ns, axiom);
  for(const auto &axiom : axioms.not_contains)
    initial_index_set(index_set, ns, axiom);
}

/// add to the index set all the indices that appear in the formulas
/// \par parameters: a list of string constraints
static void update_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const std::vector<exprt> &current_constraints)
{
  for(const auto &axiom : current_constraints)
    update_index_set(index_set, ns, axiom);
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
static void add_to_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const exprt &s,
  exprt i)
{
  simplify(i, ns);
  const bool is_size_t=expr_cast<std::size_t>(i).has_value();
  if(i.id()!=ID_constant || is_size_t)
  {
    for(const auto &sub : sub_arrays(s))
      if(index_set.cumulative[sub].insert(i).second)
        index_set.current[sub].insert(i);
  }
}

static void initial_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const string_constraintt &axiom)
{
  const symbol_exprt &qvar=axiom.univ_var();
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
        add_to_index_set(index_set, ns, s, i);
      }
      else
      {
        // otherwise we add k-1
        exprt e(i);
        const minus_exprt kminus1(
          axiom.upper_bound(),
          from_integer(1, axiom.upper_bound().type()));
        replace_expr(qvar, kminus1, e);
        add_to_index_set(index_set, ns, s, e);
      }
    }
    else
      forall_operands(it, cur)
        to_process.push_back(*it);
  }
}

static void initial_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const string_not_contains_constraintt &axiom)
{
  auto it=axiom.premise().depth_begin();
  const auto end=axiom.premise().depth_end();
  while(it!=end)
  {
    if(it->id()==ID_index)
    {
      const exprt &s=it->op0();
      const exprt &i=it->op1();

      // cur is of the form s[i] and no quantified variable appears in i
      add_to_index_set(index_set, ns, s, i);

      it.next_sibling_or_parent();
    }
    else
      ++it;
  }

  const minus_exprt kminus1(
    axiom.exists_upper_bound(),
    from_integer(1, axiom.exists_upper_bound().type()));
  add_to_index_set(index_set, ns, axiom.s1().content(), kminus1);
}

/// add to the index set all the indices that appear in the formula
/// \par parameters: a string constraint
static void update_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const exprt &formula)
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
      add_to_index_set(index_set, ns, s, simplified);
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
/// with arguments ``(str[k]=='a')``, `str`, and `k`, the function should
/// return `k`.
/// \param [in] expr: the expression to search
/// \param [in] str: the string which must be indexed
/// \param [in] qvar: the universal variable that must be in the index
/// \return an index expression in `expr` on `str` containing `qvar`
static exprt find_index(
  const exprt &expr, const exprt &str, const symbol_exprt &qvar)
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
///   t[q]='b'$, `instantiate(axiom,s,v)` would return an expression for
///   $s[v]='a' && t[v-x]='b'$.
static exprt instantiate(
  messaget::mstreamt &stream,
  const string_constraintt &axiom,
  const exprt &str,
  const exprt &val)
{
  exprt idx=find_index(axiom.body(), str, axiom.univ_var());
  if(idx.is_nil())
    return true_exprt();

  exprt r=compute_inverse_function(stream, axiom.univ_var(), val, idx);
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

/// Instantiates a quantified formula representing `not_contains` by
/// substituting the quantifiers and generating axioms.
/// \param [in] axiom: the axiom to instantiate
/// \return the lemmas produced through instantiation
static std::vector<exprt> instantiate(
  const string_not_contains_constraintt &axiom,
  const index_set_pairt &index_set,
  const string_constraint_generatort &generator)
{
  const string_exprt &s0=axiom.s0();
  const string_exprt &s1=axiom.s1();

  const auto &index_set0=index_set.cumulative.find(s0.content());
  const auto &index_set1=index_set.cumulative.find(s1.content());
  const auto &current_index_set0=index_set.current.find(s0.content());
  const auto &current_index_set1=index_set.current.find(s1.content());

  if(index_set0!=index_set.cumulative.end() &&
     index_set1!=index_set.cumulative.end() &&
     current_index_set0!=index_set.current.end() &&
     current_index_set1!=index_set.current.end())
  {
    typedef std::pair<exprt, exprt> expr_pairt;
    std::set<expr_pairt> index_pairs;

    for(const auto &ic0 : current_index_set0->second)
      for(const auto &i1 : index_set1->second)
        index_pairs.insert(expr_pairt(ic0, i1));
    for(const auto &ic1 : current_index_set1->second)
      for(const auto &i0 : index_set0->second)
        index_pairs.insert(expr_pairt(i0, ic1));

    return ::instantiate_not_contains(axiom, index_pairs, generator);
  }
  return { };
}

/// Replace array-lists by 'with' expressions.
/// For instance `array-list [ 0 , x , 1 , y ]` is replaced by
/// `ARRAYOF(0) WITH [0:=x] WITH [1:=y]`.
/// Indexes exceeding the maximal string length are ignored.
/// \param expr: an expression containing array-list expressions
/// \param string_max_length: maximum length allowed for strings
/// \return an expression containing no array-list
exprt substitute_array_lists(exprt expr, size_t string_max_length)
{
  for(auto &operand : expr.operands())
  {
    // TODO: only copy when necessary
    const exprt op(operand);
    operand=substitute_array_lists(op, string_max_length);
  }

  if(expr.id()=="array-list")
  {
    DATA_INVARIANT(
      expr.operands().size()>=2,
      string_refinement_invariantt("array-lists must have at least two "
        "operands"));
    typet &char_type=expr.operands()[1].type();
    array_typet arr_type(char_type, infinity_exprt(char_type));
    exprt ret_expr=array_of_exprt(from_integer(0, char_type), arr_type);

    for(size_t i=0; i<expr.operands().size(); i+=2)
    {
      const exprt &index=expr.operands()[i];
      const exprt &value=expr.operands()[i+1];
      const auto index_value=expr_cast<std::size_t>(index);
      if(!index.is_constant() ||
         (index_value && *index_value<string_max_length))
        ret_expr=with_exprt(ret_expr, index, value);
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
  const std::function<exprt(const exprt &)> super_get=[this](const exprt &expr)
  { return (exprt) supert::get(expr); };
  exprt ecopy(expr);
  replace_expr(symbol_resolve, ecopy);
  if(is_char_array(ns, ecopy.type()))
  {
    auto it_content=found_content.find(ecopy);
    if(it_content!=found_content.end())
      return it_content->second;

    auto it=found_length.find(ecopy);
    if(it!=found_length.end())
      return get_array(
        super_get,
        ns,
        generator.max_string_length,
        ecopy,
        it->second);
  }
  else if(ecopy.id()==ID_struct)
  {
    if(const auto string=expr_cast<string_exprt>(ecopy))
    {
      const exprt &content=string->content();
      const exprt &length=string->length();

      const exprt arr=get_array(
        super_get,
        ns,
        generator.max_string_length,
        content,
        length);
      ecopy=string_exprt(length, arr, string->type());
    }
  }

  ecopy=supert::get(ecopy);

  return substitute_array_lists(ecopy, generator.max_string_length);
}

/// Creates a solver with `axiom` as the only formula added and runs it. If it
/// is SAT, then true is returned and the given evaluation of `var` is stored
/// in `witness`. If UNSAT, then what witness is is undefined.
/// \param [in] axiom: the axiom to be checked
/// \param [in] var: the variable whose evaluation will be stored in witness
/// \return: the witness of the satisfying assignment if one
/// exists. If UNSAT, then behaviour is undefined.
static optionalt<exprt> find_counter_example(
  const namespacet &ns,
  const ui_message_handlert::uit ui,
  const exprt &axiom,
  const symbol_exprt &var)
{
  satcheck_no_simplifiert sat_check;
  bv_refinementt::infot info;
  info.ns=&ns;
  info.prop=&sat_check;
  info.refine_arithmetic=true;
  info.refine_arrays=true;
  info.max_node_refinement=5;
  info.ui=ui;
  bv_refinementt solver(info);
  solver << axiom;

  if(solver()==decision_proceduret::resultt::D_SATISFIABLE)
    return solver.get(var);
  else
    return { };
}

/// \related string_constraintt
typedef std::map<exprt, std::vector<exprt>> array_index_mapt;

/// \related string_constraintt
class gather_indices_visitort: public const_expr_visitort
{
public:
  array_index_mapt indices;

  gather_indices_visitort(): indices() {}

  void operator()(const exprt &expr) override
  {
    if(expr.id()==ID_index)
    {
      const index_exprt &index=to_index_expr(expr);
      const exprt &s(index.array());
      const exprt &i(index.index());
      indices[s].push_back(i);
    }
  }
};

/// \related string_constraintt
static array_index_mapt gather_indices(const exprt &expr)
{
  gather_indices_visitort v;
  expr.visit(v);
  return v.indices;
}

/// \related string_constraintt
class is_linear_arithmetic_expr_visitort: public const_expr_visitort
{
public:
  bool correct;

  is_linear_arithmetic_expr_visitort(): correct(true) {}

  void operator()(const exprt &expr) override
  {
    if(expr.id()!=ID_plus && expr.id()!=ID_minus && expr.id()!=ID_unary_minus)
    {
      // This represents that the expr is a valid leaf, may not be future proof
      // or 100% enforced, but is correct prescriptively. All non-sum exprs must
      // be leaves.
      correct&=expr.operands().empty();
    }
  }
};

/// \related string_constraintt
static bool is_linear_arithmetic_expr(const exprt &expr)
{
  is_linear_arithmetic_expr_visitort v;
  expr.visit(v);
  return v.correct;
}

/// The universally quantified variable is only allowed to occur in index
/// expressions in the body of a string constraint. This function returns true
/// if this is the case and false otherwise.
/// \related string_constraintt
/// \param [in] expr: The string constraint to check
/// \return true if the universal variable only occurs in index expressions,
///   false otherwise.
static bool universal_only_in_index(const string_constraintt &expr)
{
  // For efficiency, we do a depth-first search of the
  // body. The exprt visitors do a BFS and hide the stack/queue, so we would
  // need to store a map from child to parent.

  // The unsigned int represents index depth we are. For example, if we are
  // considering the fragment `a[b[x]]` (not inside an index expression), then
  // the stack would look something like `[..., (a, 0), (b, 1), (x, 2)]`.
  typedef std::pair<exprt, unsigned> valuet;
  std::stack<valuet> stack;
  // We start at 0 since expr is not an index expression, so expr.body() is not
  // in an index expression.
  stack.push(valuet(expr.body(), 0));
  while(!stack.empty())
  {
    // Inspect current value
    const valuet cur=stack.top();
    stack.pop();
    const exprt e=cur.first;
    const unsigned index_depth=cur.second;
    const unsigned child_index_depth=index_depth+(e.id()==ID_index?0:1);

    // If we found the universal variable not in an index_exprt, fail
    if(e==expr.univ_var() && index_depth==0)
      return false;
    else
      forall_operands(it, e)
        stack.push(valuet(*it, child_index_depth));
  }
  return true;
}

/// Checks the data invariant for \link string_constraintt
/// \related string_constraintt
/// \param [in] expr: the string constraint to check
/// \return whether the constraint satisfies the invariant
static bool is_valid_string_constraint(
  messaget::mstreamt &stream,
  const namespacet &ns,
  const string_constraintt &expr)
{
  const auto eom=messaget::eom;
  // Condition 1: The premise cannot contain any string indices
  const array_index_mapt premise_indices=gather_indices(expr.premise());
  if(!premise_indices.empty())
  {
    stream << "Premise has indices: " << from_expr(ns, "", expr) << ", map: {";
    for(const auto &pair : premise_indices)
    {
      stream << from_expr(ns, "", pair.first) << ": {";
      for(const auto &i : pair.second)
        stream << from_expr(ns, "", i) <<  ", ";
    }
    stream << "}}" << eom;
    return false;
  }

  const array_index_mapt body_indices=gather_indices(expr.body());
  // Must validate for each string. Note that we have an invariant that the
  // second value in the pair is non-empty.
  for(const auto &pair : body_indices)
  {
    // Condition 2: All indices of the same string must be the of the same form
    const exprt rep=pair.second.back();
    for(size_t j=0; j<pair.second.size()-1; j++)
    {
      const exprt i=pair.second[j];
      const equal_exprt equals(rep, i);
      const exprt result=simplify_expr(equals, ns);
      if(result.is_false())
      {
        stream << "Indices not equal: " << from_expr(ns, "", expr) << ", str: "
               << from_expr(ns, "", pair.first) << eom;
        return false;
      }
    }

    // Condition 3: f must be linear
    if(!is_linear_arithmetic_expr(rep))
    {
      stream << "f is not linear: " << from_expr(ns, "", expr) << ", str: "
             << from_expr(ns, "", pair.first) << eom;
      return false;
    }

    // Condition 4: the quantified variable can only occur in indices in the
    // body
    if(!universal_only_in_index(expr))
    {
      stream << "Universal variable outside of index:"
             << from_expr(ns, "", expr) << eom;
      return false;
    }
  }

  return true;
}

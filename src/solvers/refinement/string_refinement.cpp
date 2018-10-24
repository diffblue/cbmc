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
#include <numeric>
#include <stack>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/refinement/string_constraint_instantiation.h>
#include <unordered_set>
#include <util/magic.h>

static bool is_valid_string_constraint(
  messaget::mstreamt &stream,
  const namespacet &ns,
  const string_constraintt &constraint);

static optionalt<exprt> find_counter_example(
  const namespacet &ns,
  const exprt &axiom,
  const symbol_exprt &var);

/// Check axioms takes the model given by the underlying solver and answers
/// whether it satisfies the string constraints.
///
/// For each string_constraint `a`:
///   * the negation of `a` is an existential formula `b`;
///   * we substituted symbols in `b` by their values found in `get`;
///   * arrays are concretized, meaning we attribute a value for characters that
///     are unknown to get, for details see substitute_array_access;
///   * `b` is simplified and array accesses are replaced by expressions
///     without arrays;
///   * we give lemma `b` to a fresh solver;
///   * if no counter-example to `b` is found, this means the constraint `a`
///     is satisfied by the valuation given by get.
/// \return `true` if the current model satisfies all the axioms,
///         `false` otherwise with a list of lemmas which are obtained by
///         instantiating constraints at indexes given by counter-examples.
static std::pair<bool, std::vector<exprt>> check_axioms(
  const string_axiomst &axioms,
  string_constraint_generatort &generator,
  const std::function<exprt(const exprt &)> &get,
  messaget::mstreamt &stream,
  const namespacet &ns,
  bool use_counter_example,
  const union_find_replacet &symbol_resolve,
  const std::map<string_not_contains_constraintt, symbol_exprt>
    &not_contain_witnesses);

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

/// Substitute `qvar` the universally quantified variable of `axiom`, by
/// an index `val`, in `axiom`, so that the index used for `str` equals `val`.
/// For instance, if `axiom` corresponds to \f$\forall q.\ s[q+x]='a' \land
/// t[q]='b'\f$, `instantiate(axiom,s,v)` would return an expression for
/// \f$s[v]='a' \land t[v-x]='b'\f$.
/// \param stream: output stream
/// \param axiom: a universally quantified formula
/// \param str: an array of char variable
/// \param val: an index expression
/// \return `axiom` with substitued `qvar`
static exprt instantiate(
  const string_constraintt &axiom,
  const exprt &str,
  const exprt &val);

static std::vector<exprt> instantiate(
  const string_not_contains_constraintt &axiom,
  const index_set_pairt &index_set,
  const string_constraint_generatort &generator,
  const std::map<string_not_contains_constraintt, symbol_exprt> &witnesses);

static optionalt<exprt> get_array(
  const std::function<exprt(const exprt &)> &super_get,
  const namespacet &ns,
  messaget::mstreamt &stream,
  const array_string_exprt &arr);

static exprt substitute_array_access(
  const index_exprt &index_expr,
  const std::function<symbol_exprt(const irep_idt &, const typet &)>
    &symbol_generator,
  const bool left_propagate);

/// Convert index-value map to a vector of values. If a value for an
/// index is not defined, set it to the value referenced by the next higher
/// index.
/// The length of the resulting vector is the key of the map's
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
      const T &value = it->second;
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

string_refinementt::string_refinementt(const infot &info, bool)
  : supert(info),
    config_(info),
    loop_bound_(info.refinement_bound),
    generator(*info.ns)
{
}

string_refinementt::string_refinementt(const infot &info):
  string_refinementt(info, validate(info)) { }

/// Write index set to the given stream, use for debugging
static void display_index_set(
  messaget::mstreamt &stream,
  const index_set_pairt &index_set)
{
  const auto eom=messaget::eom;
  std::size_t count=0;
  std::size_t count_current=0;
  for(const auto &i : index_set.cumulative)
  {
    const exprt &s=i.first;
    stream << "IS(" << format(s) << ")=={" << eom;

    for(const auto &j : i.second)
    {
      const auto it=index_set.current.find(i.first);
      if(it!=index_set.current.end() && it->second.find(j)!=it->second.end())
      {
        count_current++;
        stream << "**";
      }
      stream << "  " << format(j) << ";" << eom;
      count++;
    }
    stream << "}"  << eom;
  }
  stream << count << " elements in index set (" << count_current
         << " newly added)" << eom;
}

/// Instantiation of all constraints
///
/// The string refinement decision procedure works with two types of quantified
/// axioms, which are of the form \f$\forall x.\ P(x)\f$ (`string_constraintt`)
/// or of the form
/// \f$\forall x. P(x) \Rightarrow \exists y .s_0[x+y] \ne s_1[y] \f$
/// (`string_not_contains_constraintt`).
/// They are instantiated in a way which depends on their form:
///   * For formulas of the form \f$\forall x.\ P(x)\f$ if string `str`
///     appears in `P` indexed by some `f(x)` and `val` is in
///     the index set of `str` we find `y` such that `f(y)=val` and
///     add lemma `P(y)`.
// NOLINTNEXTLINE(whitespace/line_length)
///     (See `instantiate(messaget::mstreamt&,const string_constraintt&,const exprt &,const exprt&)`
///      for details)
///   * For formulas of the form
///     \f$\forall x. P(x) \Rightarrow \exists y .s_0[x+y] \ne s_1[y]) \f$ we
///     need to look at the index set of both `s_0` and `s_1`.
// NOLINTNEXTLINE(whitespace/line_length)
///     (See `instantiate(const string_not_contains_constraintt&,const index_set_pairt&,const string_constraint_generatort&,const std::map<string_not_contains_constraintt, symbol_exprt>&)`
///      for details)
static std::vector<exprt> generate_instantiations(
  const string_constraint_generatort &generator,
  const index_set_pairt &index_set,
  const string_axiomst &axioms,
  const std::map<string_not_contains_constraintt, symbol_exprt>
    &not_contain_witnesses)
{
  std::vector<exprt> lemmas;
  for(const auto &i : index_set.current)
  {
    for(const auto &univ_axiom : axioms.universal)
    {
      for(const auto &j : i.second)
        lemmas.push_back(instantiate(univ_axiom, i.first, j));
    }
  }
  for(const auto &nc_axiom : axioms.not_contains)
  {
    for(const auto &instance :
        instantiate(nc_axiom, index_set, generator, not_contain_witnesses))
      lemmas.push_back(instance);
  }
  return lemmas;
}

/// Fill the array_pointer correspondence and replace the right hand sides of
/// the corresponding equations
static void make_char_array_pointer_associations(
  string_constraint_generatort &generator,
  std::vector<equal_exprt> &equations)
{
  for(equal_exprt &eq : equations)
  {
    if(
      const auto fun_app =
        expr_try_dynamic_cast<function_application_exprt>(eq.rhs()))
    {
      if(const auto result = generator.make_array_pointer_association(*fun_app))
        eq.rhs() = *result;
    }
  }
}

void replace_symbols_in_equations(
  const union_find_replacet &symbol_resolve,
  std::vector<equal_exprt> &equations)
{
  for(equal_exprt &eq : equations)
    symbol_resolve.replace_expr(eq);
}

/// Record the constraints to ensure that the expression is true when
/// the boolean is true and false otherwise.
/// \param expr: an expression of type `bool`
/// \param value: the boolean value to set it to
void string_refinementt::set_to(const exprt &expr, bool value)
{
  PRECONDITION(expr.type().id()==ID_bool);
  PRECONDITION(equality_propagation);

  if(expr.id() == ID_equal && value)
  {
    const equal_exprt &eq_expr = to_equal_expr(expr);
    equations.push_back(eq_expr);
  }
  else
  {
    INVARIANT(
      !has_char_array_subexpr(expr, ns), "char array only appear in equations");
    supert::set_to(expr, value);
  }
}

/// Add association for each char pointer in the equation
/// \param symbol_solver: a union_find_replacet object to keep track of
///   char pointer equations
/// \param equations: vector of equations
/// \param ns: namespace
/// \param stream: output stream
/// \return union_find_replacet where char pointer that have been set equal
///         by an equation are associated to the same element
static void add_equations_for_symbol_resolution(
  union_find_replacet &symbol_solver,
  const std::vector<equal_exprt> &equations,
  const namespacet &ns,
  messaget::mstreamt &stream)
{
  const auto eom = messaget::eom;
  const std::string log_message =
    "WARNING string_refinement.cpp generate_symbol_resolution_from_equations:";
  for(const equal_exprt &eq : equations)
  {
    const exprt &lhs = eq.lhs();
    const exprt &rhs = eq.rhs();
    if(lhs.id()!=ID_symbol)
    {
      stream << log_message << "non symbol lhs: " << format(lhs)
             << " with rhs: " << format(rhs) << eom;
      continue;
    }

    if(lhs.type()!=rhs.type())
    {
      stream << log_message << "non equal types lhs: " << format(lhs)
             << "\n####################### rhs: " << format(rhs) << eom;
      continue;
    }

    if(is_char_pointer_type(rhs.type()))
    {
      symbol_solver.make_union(lhs, rhs);
    }
    else if(rhs.id() == ID_function_application)
    {
      // function applications can be ignored because they will be replaced
      // in the convert_function_application step of dec_solve
    }
    else if(
      lhs.type().id() != ID_pointer && has_char_pointer_subtype(lhs.type(), ns))
    {
      if(rhs.type().id() == ID_struct)
      {
        const struct_typet &struct_type = to_struct_type(rhs.type());
        for(const auto &comp : struct_type.components())
        {
          if(is_char_pointer_type(comp.type()))
          {
            const member_exprt lhs_data(lhs, comp.get_name(), comp.type());
            const exprt rhs_data = simplify_expr(
              member_exprt(rhs, comp.get_name(), comp.type()), ns);
            symbol_solver.make_union(lhs_data, rhs_data);
          }
        }
      }
      else
      {
        stream << log_message << "non struct with char pointer subexpr "
               << format(rhs) << "\n  * of type " << format(rhs.type()) << eom;
      }
    }
  }
}

/// This is meant to be used on the lhs of an equation with string subtype.
/// \param lhs: expression which is either of string type, or a symbol
///   representing a struct with some string members
/// \return if lhs is a string return this string, if it is a struct return the
///   members of the expression that have string type.
static std::vector<exprt> extract_strings_from_lhs(const exprt &lhs)
{
  std::vector<exprt> result;
  if(lhs.type() == string_typet())
    result.push_back(lhs);
  else if(lhs.type().id() == ID_struct)
  {
    const struct_typet &struct_type = to_struct_type(lhs.type());
    for(const auto &comp : struct_type.components())
    {
      const std::vector<exprt> strings_in_comp = extract_strings_from_lhs(
        member_exprt(lhs, comp.get_name(), comp.type()));
      result.insert(
        result.end(), strings_in_comp.begin(), strings_in_comp.end());
    }
  }
  return result;
}

/// \param expr: an expression
/// \return all subexpressions of type string which are not if_exprt expressions
///   this includes expressions of the form `e.x` if e is a symbol subexpression
///   with a field `x` of type string
static std::vector<exprt> extract_strings(const exprt &expr)
{
  std::vector<exprt> result;
  for(auto it = expr.depth_begin(); it != expr.depth_end();)
  {
    if(it->type() == string_typet() && it->id() != ID_if)
    {
      result.push_back(*it);
      it.next_sibling_or_parent();
    }
    else if(it->id() == ID_symbol)
    {
      for(const exprt &e : extract_strings_from_lhs(*it))
        result.push_back(e);
      it.next_sibling_or_parent();
    }
    else
      ++it;
  }
  return result;
}

/// Given an equation on strings, mark these strings as belonging to the same
/// set in the `symbol_resolve` structure. The lhs and rhs of the equation,
/// should have string type or be struct with string members.
/// \param eq: equation to add
/// \param symbol_resolve: structure to which the equation will be added
/// \param ns: namespace
static void add_string_equation_to_symbol_resolution(
  const equal_exprt &eq,
  union_find_replacet &symbol_resolve,
  const namespacet &ns)
{
  if(eq.rhs().type() == string_typet())
  {
    symbol_resolve.make_union(eq.lhs(), eq.rhs());
  }
  else if(has_subtype(eq.lhs().type(), ID_string, ns))
  {
    if(eq.rhs().type().id() == ID_struct)
    {
      const struct_typet &struct_type = to_struct_type(eq.rhs().type());
      for(const auto &comp : struct_type.components())
      {
        const member_exprt lhs_data(eq.lhs(), comp.get_name(), comp.type());
        const exprt rhs_data = simplify_expr(
          member_exprt(eq.rhs(), comp.get_name(), comp.type()), ns);
        add_string_equation_to_symbol_resolution(
          equal_exprt(lhs_data, rhs_data), symbol_resolve, ns);
      }
    }
  }
}

/// Symbol resolution for expressions of type string typet.
/// We record equality between these expressions in the output if one of the
/// function calls depends on them.
/// \param equations: list of equations
/// \param ns: namespace
/// \param stream: output stream
/// \return union_find_replacet structure containing the correspondences.
union_find_replacet string_identifiers_resolution_from_equations(
  std::vector<equal_exprt> &equations,
  const namespacet &ns,
  messaget::mstreamt &stream)
{
  const auto eom = messaget::eom;
  const std::string log_message =
    "WARNING string_refinement.cpp "
    "string_identifiers_resolution_from_equations:";

  equation_symbol_mappingt equation_map;

  // Indexes of equations that need to be added to the result
  std::unordered_set<size_t> required_equations;
  std::stack<size_t> equations_to_treat;

  for(std::size_t i = 0; i < equations.size(); ++i)
  {
    const equal_exprt &eq = equations[i];
    if(eq.rhs().id() == ID_function_application)
    {
      if(required_equations.insert(i).second)
        equations_to_treat.push(i);

      std::vector<exprt> rhs_strings = extract_strings(eq.rhs());
      for(const auto &expr : rhs_strings)
        equation_map.add(i, expr);
    }
    else if(
      eq.lhs().type().id() != ID_pointer &&
      has_subtype(eq.lhs().type(), ID_string, ns))
    {
      std::vector<exprt> lhs_strings = extract_strings_from_lhs(eq.lhs());

      for(const auto &expr : lhs_strings)
        equation_map.add(i, expr);

      if(lhs_strings.empty())
      {
        stream << log_message << "non struct with string subtype "
               << format(eq.lhs()) << "\n  * of type "
               << format(eq.lhs().type()) << eom;
      }

      for(const exprt &expr : extract_strings(eq.rhs()))
        equation_map.add(i, expr);
    }
  }

  // transitively add all equations which depend on the equations to treat
  while(!equations_to_treat.empty())
  {
    const std::size_t i = equations_to_treat.top();
    equations_to_treat.pop();
    for(const exprt &string : equation_map.find_expressions(i))
    {
      for(const std::size_t j : equation_map.find_equations(string))
      {
        if(required_equations.insert(j).second)
          equations_to_treat.push(j);
      }
    }
  }

  union_find_replacet result;
  for(const std::size_t i : required_equations)
    add_string_equation_to_symbol_resolution(equations[i], result, ns);

  return result;
}

#ifdef DEBUG
/// Output a vector of equations to the given stream, used for debugging.
static void output_equations(
  std::ostream &output,
  const std::vector<equal_exprt> &equations)
{
  for(std::size_t i = 0; i < equations.size(); ++i)
    output << "  [" << i << "] " << format(equations[i].lhs())
           << " == " << format(equations[i].rhs()) << std::endl;
}
#endif

/// Main decision procedure of the solver. Looks for a valuation of variables
/// compatible with the constraints that have been given to `set_to` so far.
///
/// The decision procedure initiated by string_refinementt::dec_solve is
/// composed of several steps detailed below.
///
/// ## Symbol resolution
/// Pointer symbols which are set to be equal by constraints, are replaced by
/// an single symbol in the solver. The `symbol_solvert` object used for this
/// substitution is constructed by
// NOLINTNEXTLINE
/// `generate_symbol_resolution_from_equations(const std::vector<equal_exprt>&,const namespacet&,messaget::mstreamt&)`.
/// All these symbols are then replaced using
// NOLINTNEXTLINE
/// `replace_symbols_in_equations(const union_find_replacet &, std::vector<equal_exprt> &)`.
///
/// ## Conversion to first order formulas:
/// Each string primitive is converted to a list of first order formulas by the
// NOLINTNEXTLINE
/// function `substitute_function_applications_in_equations(std::vector<equal_exprt>&,string_constraint_generatort&)`.
/// These formulas should be unquantified or be either a `string_constraintt`
/// or a `string_not_contains_constraintt`.
/// The constraints corresponding to each primitive can be found by following
/// the links in section \ref primitives.
///
/// Since only arrays appear in the string constraints, during the conversion to
/// first order formulas, pointers are associated to arrays.
/// The `string_constraint_generatort` object keeps track of this association.
/// It can either be set manually using the primitives
/// `cprover_associate_array_to_pointer` or a fresh array is created.
///
/// ## Refinement loop
/// We use `super_dec_solve` and `super_get` to denote the methods of the
/// underlying solver (`bv_refinementt` by default).
/// The refinement loop relies on functions `string_refinementt::check_axioms`
/// which returns true when the set of quantified constraints `q` is satisfied
/// by the valuation given by`super_get` and
/// `string_refinementt::instantiate` which gives propositional formulas
/// implied by a string constraint.
/// If the following algorithm returns `SAT` or `UNSAT`, the given constraints
/// are `SAT` or `UNSAT` respectively:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// is_SAT(unquantified_constraints uq, quantified_constraints q)
/// {
///   cur <- uq;
///   while(limit--) > 0
///   {
///     if(super_dec_solve(cur)==SAT)
///     {
///       if(check_axioms(q, super_get))
///       else
///         for(axiom in q)
///           cur.add(instantiate(axiom));
///         return SAT;
///     }
///     else
///       return UNSAT;
///   }
///   return ERROR;
/// }
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// \return `resultt::D_SATISFIABLE` if the constraints are satisfiable,
///   `resultt::D_UNSATISFIABLE` if they are unsatisfiable,
///   `resultt::D_ERROR` if the limit of iteration was reached.
decision_proceduret::resultt string_refinementt::dec_solve()
{
#ifdef DEBUG
  debug() << "dec_solve: Initial set of equations" << eom;
  output_equations(debug(), equations);
#endif

  debug() << "dec_solve: Build symbol solver from equations" << eom;
  // symbol_resolve is used by get and is kept between calls to dec_solve,
  // that's why we use a class member here
  add_equations_for_symbol_resolution(symbol_resolve, equations, ns, debug());
#ifdef DEBUG
  debug() << "symbol resolve:" << eom;
  for(const auto &pair : symbol_resolve.to_vector())
    debug() << format(pair.first) << " --> " << format(pair.second) << eom;
#endif

  const union_find_replacet string_id_symbol_resolve =
    string_identifiers_resolution_from_equations(equations, ns, debug());
#ifdef DEBUG
  debug() << "symbol resolve string:" << eom;
  for(const auto &pair : string_id_symbol_resolve.to_vector())
  {
    debug() << format(pair.first) << " --> " << format(pair.second) << eom;
  }
#endif

  debug() << "dec_solve: Replacing string ids in function applications" << eom;
  for(equal_exprt &eq : equations)
  {
    if(can_cast_expr<function_application_exprt>(eq.rhs()))
      string_id_symbol_resolve.replace_expr(eq.rhs());
  }

  // Generator is also used by get, so we have to use it as a class member
  // but we make sure it is cleared at each `dec_solve` call.
  generator.constraints.clear();
  make_char_array_pointer_associations(generator, equations);

#ifdef DEBUG
  output_equations(debug(), equations);
#endif

  debug() << "dec_solve: compute dependency graph and remove function "
          << "applications captured by the dependencies:" << eom;
  std::vector<equal_exprt> local_equations;
  for(const equal_exprt &eq : equations)
  {
    equal_exprt eq_copy = eq;
    // Char array symbols are replaced by cannonical element to ensure
    // equal arrays are associated to the same nodes in the graph.
    symbol_resolve.replace_expr(eq_copy);
    if(!add_node(dependencies, eq_copy, generator.array_pool))
      local_equations.push_back(eq);
  }
  equations.clear();

#ifdef DEBUG
  dependencies.output_dot(debug());
#endif

  debug() << "dec_solve: add constraints" << eom;
  dependencies.add_constraints(generator);

#ifdef DEBUG
  output_equations(debug(), equations);
#endif

#ifdef DEBUG
  debug() << "dec_solve: arrays_of_pointers:" << eom;
  for(auto pair : generator.array_pool.get_arrays_of_pointers())
  {
    debug() << "  * " << format(pair.first) << "\t--> " << format(pair.second)
            << " : " << format(pair.second.type()) << eom;
  }
#endif

  for(const auto &eq : local_equations)
  {
#ifdef DEBUG
    debug() << "dec_solve: set_to " << format(eq) << eom;
#endif
    supert::set_to(eq, true);
  }

  std::transform(
    generator.constraints.universal.begin(),
    generator.constraints.universal.end(),
    std::back_inserter(axioms.universal),
    [&](string_constraintt constraint) {
      constraint.replace_expr(symbol_resolve);
      DATA_INVARIANT(
        is_valid_string_constraint(error(), ns, constraint),
        string_refinement_invariantt(
          "string constraints satisfy their invariant"));
      return constraint;
    });

  std::transform(
    generator.constraints.not_contains.begin(),
    generator.constraints.not_contains.end(),
    std::back_inserter(axioms.not_contains),
    [&](string_not_contains_constraintt axiom) {
      symbol_resolve.replace_expr(axiom);
      return axiom;
    });

  // Used to store information about witnesses for not_contains constraints
  std::map<string_not_contains_constraintt, symbol_exprt> not_contain_witnesses;
  for(const auto &nc_axiom : axioms.not_contains)
  {
    const auto &witness_type = [&] {
      const auto &rtype = to_array_type(nc_axiom.s0().type());
      const typet &index_type = rtype.size().type();
      return array_typet(index_type, infinity_exprt(index_type));
    }();
    not_contain_witnesses[nc_axiom] =
      generator.fresh_symbol("not_contains_witness", witness_type);
  }

  for(const exprt &lemma : generator.constraints.existential)
    add_lemma(lemma);

  // Initial try without index set
  const auto get = [this](const exprt &expr) { return this->get(expr); };
  dependencies.clean_cache();
  const decision_proceduret::resultt res=supert::dec_solve();
  if(res==resultt::D_SATISFIABLE)
  {
    bool satisfied;
    std::vector<exprt> counter_examples;
    std::tie(satisfied, counter_examples) = check_axioms(
      axioms,
      generator,
      get,
      debug(),
      ns,
      config_.use_counter_example,
      symbol_resolve,
      not_contain_witnesses);
    if(satisfied)
    {
      debug() << "check_SAT: the model is correct" << eom;
      return resultt::D_SATISFIABLE;
    }
    debug() << "check_SAT: got SAT but the model is not correct" << eom;
  }
  else
  {
    debug() << "check_SAT: got UNSAT or ERROR" << eom;
    return res;
  }

  initial_index_set(index_sets, ns, axioms);
  update_index_set(index_sets, ns, current_constraints);
  current_constraints.clear();
  const auto instances = generate_instantiations(
    generator, index_sets, axioms, not_contain_witnesses);
  for(const auto &instance : instances)
    add_lemma(instance);

  while((loop_bound_--)>0)
  {
    dependencies.clean_cache();
    const decision_proceduret::resultt res=supert::dec_solve();

    if(res==resultt::D_SATISFIABLE)
    {
      bool satisfied;
      std::vector<exprt> counter_examples;
      std::tie(satisfied, counter_examples) = check_axioms(
        axioms,
        generator,
        get,
        debug(),
        ns,
        config_.use_counter_example,
        symbol_resolve,
        not_contain_witnesses);
      if(satisfied)
      {
        debug() << "check_SAT: the model is correct" << eom;
        return resultt::D_SATISFIABLE;
      }

      debug() << "check_SAT: got SAT but the model is not correct, refining..."
              << eom;

      // Since the model is not correct although we got SAT, we need to refine
      // the property we are checking by adding more indices to the index set,
      // and instantiating universal formulas with this indices.
      // We will then relaunch the solver with these added lemmas.
      index_sets.current.clear();
      update_index_set(index_sets, ns, current_constraints);

      display_index_set(debug(), index_sets);

      if(index_sets.current.empty())
      {
        if(axioms.not_contains.empty())
        {
          error() << "dec_solve: current index set is empty, "
                  << "this should not happen" << eom;
          return resultt::D_ERROR;
        }
        else
        {
          debug() << "dec_solve: current index set is empty, "
                  << "adding counter examples" << eom;
          for(const auto &counter : counter_examples)
            add_lemma(counter);
        }
      }
      current_constraints.clear();
      const auto instances = generate_instantiations(
        generator, index_sets, axioms, not_contain_witnesses);
      for(const auto &instance : instances)
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

/// Add the given lemma to the solver.
/// \param lemma: a Boolean expression
/// \param simplify_lemma: whether the lemma should be simplified before being
///        given to the underlying solver.
void string_refinementt::add_lemma(
  const exprt &lemma,
  const bool simplify_lemma)
{
  if(!seen_instances.insert(lemma).second)
    return;

  current_constraints.push_back(lemma);

  exprt simple_lemma=lemma;
  if(simplify_lemma)
    simplify(simple_lemma, ns);

  if(simple_lemma.is_true())
  {
#if 0
    debug() << "string_refinementt::add_lemma : tautology" << eom;
#endif
    return;
  }

  symbol_resolve.replace_expr(simple_lemma);

  // Replace empty arrays with array_of expression because the solver cannot
  // handle empty arrays.
  for(auto it = simple_lemma.depth_begin(); it != simple_lemma.depth_end();)
  {
    if(it->id() == ID_array && it->operands().empty())
    {
      it.mutate() = array_of_exprt(
        from_integer(CHARACTER_FOR_UNKNOWN, it->type().subtype()),
        to_array_type(it->type()));
      it.next_sibling_or_parent();
    }
    else
      ++it;
  }

  debug() << "adding lemma " << format(simple_lemma) << eom;

  prop.l_set_to_true(convert(simple_lemma));
}

/// Get a model of an array and put it in a certain form.
/// If the model is incomplete or if it is too big, return no value.
/// \param super_get: function returning the valuation of an expression
///        in a model
/// \param ns: namespace
/// \param stream: output stream for warning messages
/// \param arr: expression of type array representing a string
/// \return an optional array expression or array_of_exprt
static optionalt<exprt> get_array(
  const std::function<exprt(const exprt &)> &super_get,
  const namespacet &ns,
  messaget::mstreamt &stream,
  const array_string_exprt &arr)
{
  const auto eom = messaget::eom;
  const exprt &size = arr.length();
  exprt arr_val = simplify_expr(super_get(arr), ns);
  exprt size_val=super_get(size);
  size_val=simplify_expr(size_val, ns);
  const typet char_type = arr.type().subtype();
  const typet &index_type=size.type();
  const array_typet empty_ret_type(char_type, from_integer(0, index_type));
  const array_of_exprt empty_ret(from_integer(0, char_type), empty_ret_type);

  if(size_val.id()!=ID_constant)
  {
    stream << "(sr::get_array) string of unknown size: " << format(size_val)
           << eom;
    return {};
  }

  auto n_opt = numeric_cast<std::size_t>(size_val);
  if(!n_opt)
  {
    stream << "(sr::get_array) size is not valid" << eom;
    return {};
  }
  std::size_t n = *n_opt;

  if(n > MAX_CONCRETE_STRING_SIZE)
  {
    stream << "(sr::get_array) long string (size " << format(arr.length())
           << " = " << n << ") " << format(arr) << eom;
    stream << "(sr::get_array) consider reducing max-nondet-string-length so "
              "that no string exceeds "
           << MAX_CONCRETE_STRING_SIZE
           << " in length and "
              "make sure all functions returning strings are loaded"
           << eom;
    stream << "(sr::get_array) this can also happen on invalid object access"
           << eom;
    return nil_exprt();
  }

  if(
    const auto &array = interval_sparse_arrayt::of_expr(
      arr_val, from_integer(CHARACTER_FOR_UNKNOWN, char_type)))
    return array->concretize(n, index_type);
  return {};
}

/// convert the content of a string to a more readable representation. This
/// should only be used for debugging.
/// \param arr: a constant array expression
/// \return a string
static std::string string_of_array(const array_exprt &arr)
{
  if(arr.type().id()!=ID_array)
      return std::string("");

  exprt size_expr=to_array_type(arr.type()).size();
  auto n = numeric_cast_v<std::size_t>(size_expr);
  return utf16_constant_array_to_java(arr, n);
}

/// Debugging function which finds the valuation of the given array in
/// `super_get` and concretize unknown characters.
/// \param super_get: give a valuation to variables
/// \param ns: namespace
/// \param stream: output stream
/// \param arr: array expression
/// \return expression corresponding to `arr` in the model
static exprt get_char_array_and_concretize(
  const std::function<exprt(const exprt &)> &super_get,
  const namespacet &ns,
  messaget::mstreamt &stream,
  const array_string_exprt &arr)
{
  const auto &eom = messaget::eom;
  stream << "- " << format(arr) << ":\n";
  stream << std::string(4, ' ') << "- type: " << format(arr.type()) << eom;
  const auto arr_model_opt =
    get_array(super_get, ns, stream, arr);
  if(arr_model_opt)
  {
    stream << std::string(4, ' ') << "- char_array: " << format(*arr_model_opt)
           << '\n';
    stream << std::string(4, ' ') << "- type : " << format(arr_model_opt->type())
           << eom;
    const exprt simple = simplify_expr(*arr_model_opt, ns);
    stream << std::string(4, ' ') << "- simplified_char_array: " << format(simple)
           << eom;
    if(
      const auto concretized_array = get_array(
        super_get, ns, stream, to_array_string_expr(simple)))
    {
      stream << std::string(4, ' ')
             << "- concretized_char_array: " << format(*concretized_array)
             << eom;

      if(
        const auto array_expr =
          expr_try_dynamic_cast<array_exprt>(*concretized_array))
      {
        stream << std::string(4, ' ') << "- as_string: \""
               << string_of_array(*array_expr) << "\"\n";
      }
      else
        stream << std::string(2, ' ') << "- warning: not an array" << eom;
      return *concretized_array;
    }
    return simple;
  }
  stream << std::string(4, ' ') << "- incomplete model" << eom;
  return arr;
}

/// Display part of the current model by mapping the variables created by the
/// solver to constant expressions given by the current model
void debug_model(
  const string_constraint_generatort &generator,
  messaget::mstreamt &stream,
  const namespacet &ns,
  const std::function<exprt(const exprt &)> &super_get,
  const std::vector<symbol_exprt> &symbols)
{
  stream << "debug_model:" << '\n';
  for(const auto &pointer_array : generator.array_pool.get_arrays_of_pointers())
  {
    const auto arr = pointer_array.second;
    const exprt model = get_char_array_and_concretize(
      super_get, ns, stream, arr);

    stream << "- " << format(arr) << ":\n"
           << "  - pointer: " << format(pointer_array.first) << "\n"
           << "  - model: " << format(model) << messaget::eom;
  }

  for(const auto &symbol : symbols)
  {
    stream << " - " << symbol.get_identifier() << ": "
           << format(super_get(symbol)) << '\n';
  }
  stream << messaget::eom;
}

/// Create a new expression where 'with' expressions on arrays are replaced by
/// 'if' expressions. e.g. for an array access arr[index], where: `arr :=
/// array_of(12) with {0:=24} with {2:=42}` the constructed expression will be:
/// `index==0 ? 24 : index==2 ? 42 : 12`
/// If `left_propagate` is set to true, the expression will look like
/// `index<=0 ? 24 : index<=2 ? 42 : 12`
/// \param expr: A (possibly nested) 'with' expression on an `array_of`
///   expression. The function checks that the expression is of the form
///   `with_expr(with_expr(...(array_of(...)))`. This is the form in which
///   array valuations coming from the underlying solver are given.
/// \param index: An index with which to build the equality condition
/// \return An expression containing no 'with' expression
static exprt substitute_array_access(
  const with_exprt &expr,
  const exprt &index,
  const bool left_propagate)
{
  return left_propagate ? interval_sparse_arrayt(expr).to_if_expression(index)
                        : sparse_arrayt::to_if_expression(expr, index);
}

/// Create an equivalent expression where array accesses are replaced by 'if'
/// expressions: for instance in array access `arr[index]`, where:
/// `arr := {12, 24, 48}` the constructed expression will be:
///    `index==0 ? 12 : index==1 ? 24 : 48`
/// Avoids repetition so `arr := {12, 12, 24, 48}` will give
///    `index<=1 ? 12 : index==1 ? 24 : 48`
static exprt substitute_array_access(
  const array_exprt &array_expr,
  const exprt &index,
  const std::function<symbol_exprt(const irep_idt &, const typet &)>
    &symbol_generator)
{
  const typet &char_type = array_expr.type().subtype();
  const exprt default_val = symbol_generator("out_of_bound_access", char_type);
  const interval_sparse_arrayt sparse_array(array_expr, default_val);
  return sparse_array.to_if_expression(index);
}

static exprt substitute_array_access(
  const if_exprt &if_expr,
  const exprt &index,
  const std::function<symbol_exprt(const irep_idt &, const typet &)>
    &symbol_generator,
  const bool left_propagate)
{
  // Substitute recursively in branches of conditional expressions
  const exprt true_case = substitute_array_access(
    index_exprt(if_expr.true_case(), index), symbol_generator, left_propagate);
  const exprt false_case = substitute_array_access(
    index_exprt(if_expr.false_case(), index), symbol_generator, left_propagate);

  return if_exprt(if_expr.cond(), true_case, false_case);
}

static exprt substitute_array_access(
  const index_exprt &index_expr,
  const std::function<symbol_exprt(const irep_idt &, const typet &)>
    &symbol_generator,
  const bool left_propagate)
{
  const exprt &array = index_expr.array();
  if(auto array_of = expr_try_dynamic_cast<array_of_exprt>(array))
    return array_of->op();
  if(auto array_with = expr_try_dynamic_cast<with_exprt>(array))
    return substitute_array_access(
      *array_with, index_expr.index(), left_propagate);
  if(auto array_expr = expr_try_dynamic_cast<array_exprt>(array))
    return substitute_array_access(
      *array_expr, index_expr.index(), symbol_generator);
  if(auto if_expr = expr_try_dynamic_cast<if_exprt>(array))
    return substitute_array_access(
      *if_expr, index_expr.index(), symbol_generator, left_propagate);

  INVARIANT(
    array.is_nil() || array.id() == ID_symbol,
    std::string(
      "in case the array is unknown, it should be a symbol or nil, id: ")
    + id2string(array.id()));
  return index_expr;
}

/// Auxiliary function for substitute_array_access
/// Performs the same operation but modifies the argument instead of returning
/// the resulting expression.
static void substitute_array_access_in_place(
  exprt &expr,
  const std::function<symbol_exprt(const irep_idt &, const typet &)>
    &symbol_generator,
  const bool left_propagate)
{
  if(const auto index_expr = expr_try_dynamic_cast<index_exprt>(expr))
  {
    expr =
      substitute_array_access(*index_expr, symbol_generator, left_propagate);
  }

  for(auto &op : expr.operands())
    substitute_array_access_in_place(op, symbol_generator, left_propagate);
}

/// Create an equivalent expression where array accesses and 'with' expressions
/// are replaced by 'if' expressions, in particular:
///  * for an array access `arr[index]`, where:
///    `arr := {12, 24, 48}` the constructed expression will be:
///    `index==0 ? 12 : index==1 ? 24 : 48`
///  * for an array access `arr[index]`, where:
///    `arr := array_of(12) with {0:=24} with {2:=42}` the constructed
///    expression will be: `index==0 ? 24 : index==2 ? 42 : 12`
///  * for an array access `(g1?arr1:arr2)[x]` where `arr1 := {12}` and
///    `arr2 := {34}`, the constructed expression will be: `g1 ? 12 : 34`
///  * for an access in an empty array `{ }[x]` returns a fresh symbol, this
///    corresponds to a non-deterministic result
/// Note that if left_propagate is set to true, the `with` case will result in
/// something like: `index <= 0 ? 24 : index <= 2 ? 42 : 12`
/// \param expr: an expression containing array accesses
/// \param symbol_generator: function which given a prefix and a type generates
///        a fresh symbol of the given type
/// \param left_propagate: should values be propagated to the left in with
///        expressions
/// \return an expression containing no array access
exprt substitute_array_access(
  exprt expr,
  const std::function<symbol_exprt(const irep_idt &, const typet &)>
    &symbol_generator,
  const bool left_propagate)
{
  substitute_array_access_in_place(expr, symbol_generator, left_propagate);
  return expr;
}

/// Negates the constraint to be fed to a solver. The intended usage is to find
/// an assignment of the universal variable that would violate the axiom. To
/// avoid false positives, the symbols other than the universal variable should
/// have been replaced by their valuation in the current model.
/// \pre Symbols other than the universal variable should have been replaced by
///   their valuation in the current model.
/// \param constraint: the not_contains constraint to add the negation of
/// \param univ_var: the universal variable for the negation of the axiom
/// \param get: valuation function, the result should have been simplified
/// \return: the negation of the axiom under the current evaluation
static exprt negation_of_not_contains_constraint(
  const string_not_contains_constraintt &constraint,
  const symbol_exprt &univ_var,
  const std::function<exprt(const exprt &)> &get)
{
  // If the for all is vacuously true, the negation is false.
  const auto lbe =
    numeric_cast_v<mp_integer>(get(constraint.exists_lower_bound()));
  const auto ube =
    numeric_cast_v<mp_integer>(get(constraint.exists_upper_bound()));
  const auto univ_bounds = and_exprt(
    binary_relation_exprt(get(constraint.univ_lower_bound()), ID_le, univ_var),
    binary_relation_exprt(get(constraint.univ_upper_bound()), ID_gt, univ_var));

  // The negated existential becomes an universal, and this is the unrolling of
  // that universal quantifier.
  std::vector<exprt> conjuncts;
  conjuncts.reserve(numeric_cast_v<std::size_t>(ube - lbe));
  for(mp_integer i=lbe; i<ube; ++i)
  {
    const constant_exprt i_expr = from_integer(i, univ_var.type());
    const exprt s0_char =
      get(index_exprt(constraint.s0(), plus_exprt(univ_var, i_expr)));
    const exprt s1_char = get(index_exprt(constraint.s1(), i_expr));
    conjuncts.push_back(equal_exprt(s0_char, s1_char));
  }
  const exprt equal_strings = conjunction(conjuncts);
  return and_exprt(univ_bounds, get(constraint.premise()), equal_strings);
}

/// Debugging function which outputs the different steps an axiom goes through
/// to be checked in check axioms.
/// \tparam T: can be either string_constraintt or
///   string_not_contains_constraintt
template <typename T>
static void debug_check_axioms_step(
  messaget::mstreamt &stream,
  const T &axiom,
  const T &axiom_in_model,
  const exprt &negaxiom,
  const exprt &with_concretized_arrays)
{
  stream << std::string(4, ' ') << "- axiom:\n" << std::string(6, ' ');
  stream << to_string(axiom);
  stream << '\n' << std::string(4, ' ') << "- axiom_in_model:\n"
         << std::string(6, ' ');
  stream << to_string(axiom_in_model) << '\n'
         << std::string(4, ' ') << "- negated_axiom:\n"
         << std::string(6, ' ') << format(negaxiom) << '\n';
  stream << std::string(4, ' ') << "- negated_axiom_with_concretized_arrays:\n"
         << std::string(6, ' ') << format(with_concretized_arrays) << '\n';
}

/// \return true if the current model satisfies all the axioms
static std::pair<bool, std::vector<exprt>> check_axioms(
  const string_axiomst &axioms,
  string_constraint_generatort &generator,
  const std::function<exprt(const exprt &)> &get,
  messaget::mstreamt &stream,
  const namespacet &ns,
  bool use_counter_example,
  const union_find_replacet &symbol_resolve,
  const std::map<string_not_contains_constraintt, symbol_exprt>
    &not_contain_witnesses)
{
  const auto eom=messaget::eom;
  // clang-format off
  const auto gen_symbol = [&](const irep_idt &id, const typet &type)
  {
    return generator.fresh_symbol(id, type);
  };
  // clang-format on

  stream << "string_refinementt::check_axioms:" << eom;

  stream << "symbol_resolve:" << eom;
  auto pairs = symbol_resolve.to_vector();
  for(const auto &pair : pairs)
    stream << "  - " << format(pair.first) << " --> " << format(pair.second)
           << eom;

#ifdef DEBUG
  debug_model(
    generator, stream, ns, get, generator.fresh_symbol.created_symbols);
#endif

  // Maps from indexes of violated universal axiom to a witness of violation
  std::map<size_t, exprt> violated;

  stream << "string_refinement::check_axioms: " << axioms.universal.size()
         << " universal axioms:" << eom;
  for(size_t i=0; i<axioms.universal.size(); i++)
  {
    const string_constraintt &axiom=axioms.universal[i];
    const string_constraintt axiom_in_model(
      axiom.univ_var,
      get(axiom.lower_bound),
      get(axiom.upper_bound),
      get(axiom.body));

    exprt negaxiom = axiom_in_model.negation();
    negaxiom = simplify_expr(negaxiom, ns);

    stream << std::string(2, ' ') << i << ".\n";
    const exprt with_concretized_arrays =
      substitute_array_access(negaxiom, gen_symbol, true);
    debug_check_axioms_step(
      stream, axiom, axiom_in_model, negaxiom, with_concretized_arrays);

    if(
      const auto &witness =
        find_counter_example(ns, with_concretized_arrays, axiom.univ_var))
    {
      stream << std::string(4, ' ') << "- violated_for: "
             << format(axiom.univ_var) << "=" << format(*witness) << eom;
      violated[i]=*witness;
    }
    else
      stream << std::string(4, ' ') << "- correct" << eom;
  }

  // Maps from indexes of violated not_contains axiom to a witness of violation
  std::map<std::size_t, exprt> violated_not_contains;

  stream << "there are " << axioms.not_contains.size()
         << " not_contains axioms" << eom;
  for(std::size_t i = 0; i < axioms.not_contains.size(); i++)
  {
    const string_not_contains_constraintt &nc_axiom=axioms.not_contains[i];
    const symbol_exprt univ_var = generator.fresh_symbol(
      "not_contains_univ_var", nc_axiom.s0().length().type());
    const exprt negated_axiom = negation_of_not_contains_constraint(
      nc_axiom, univ_var, [&](const exprt &expr) {
        return simplify_expr(get(expr), ns); });

    stream << std::string(2, ' ') << i << ".\n";
    debug_check_axioms_step(
      stream, nc_axiom, nc_axiom, negated_axiom, negated_axiom);

    if(
      const auto witness =
        find_counter_example(ns, negated_axiom, univ_var))
    {
      stream << std::string(4, ' ') << "- violated_for: "
             << univ_var.get_identifier() << "=" << format(*witness) << eom;
      violated_not_contains[i]=*witness;
    }
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
      std::vector<exprt> lemmas;

      for(const auto &v : violated)
      {
        const exprt &val=v.second;
        const string_constraintt &axiom=axioms.universal[v.first];

        exprt instance(axiom.body);
        replace_expr(axiom.univ_var, val, instance);
        // We are not sure the index set contains only positive numbers
        and_exprt bounds(
          axiom.univ_within_bounds(),
          binary_relation_exprt(from_integer(0, val.type()), ID_le, val));
        replace_expr(axiom.univ_var, val, bounds);
        const implies_exprt counter(bounds, instance);
        lemmas.push_back(counter);
      }

      for(const auto &v : violated_not_contains)
      {
        const exprt &val=v.second;
        const string_not_contains_constraintt &axiom=
          axioms.not_contains[v.first];

        const exprt func_val =
          index_exprt(not_contain_witnesses.at(axiom), val);
        const exprt comp_val=simplify_sum(plus_exprt(val, func_val));

        std::set<std::pair<exprt, exprt>> indices;
        indices.insert(std::pair<exprt, exprt>(comp_val, func_val));
        const exprt counter =
          ::instantiate_not_contains(axiom, indices, not_contain_witnesses)[0];
        lemmas.push_back(counter);
      }
      return { false, lemmas };
    }
  }
  return { false, std::vector<exprt>() };
}

/// \param f: an expression with only addition and subtraction
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

/// \param m: a map from expressions to integers
/// \param type: type for the returned expression
/// \param negated: optinal Boolean asking to negates the sum
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
      const auto int_value = numeric_cast_v<mp_integer>(to_constant_expr(t));
      constants += int_value * second;
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

/// \param f: an expression with only plus and minus expr
/// \return an equivalent expression in a canonical form
exprt simplify_sum(const exprt &f)
{
  std::map<exprt, int> map=map_representation_of_sum(f);
  return sum_over_map(map, f.type());
}

/// \param stream: an output stream
/// \param qvar: a symbol representing a universally quantified variable
/// \param val: an expression
/// \param f: an expression containing `+` and `-`
/// operations in which `qvar` should appear exactly once.
/// \return an expression corresponding of $f^{-1}(val)$ where $f$ is seen as
///   a function of $qvar$, i.e. the value that is necessary for `qvar` for `f`
///   to be equal to `val`. For instance, if `f` corresponds to the expression
///   $q + x$, `compute_inverse_function(q,v,f)` returns an expression
///   for $v - x$.
static exprt compute_inverse_function(
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
      it->second == 0,
      string_refinement_invariantt(
        "a proper function must have exactly one "
        "occurrences after reduction, or it cancelled out, and it does not"
        " have one"));
  }

  elems.erase(it);
  return sum_over_map(elems, f.type(), neg);
}

class find_qvar_visitort : public const_expr_visitort
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
/// \param index: an index expression
/// \param qvar: a symbol expression
/// \return a Boolean
static bool find_qvar(const exprt &index, const symbol_exprt &qvar)
{
  find_qvar_visitort v2(qvar);
  index.visit(v2);
  return v2.found;
}

/// Add to the index set all the indices that appear in the formulas and the
/// upper bound minus one.
/// \param index_set: set of indexes to update
/// \param ns: namespace
/// \param axioms: a list of string axioms
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

/// Add to the index set all the indices that appear in the formulas.
/// \param index_set: set of indexes to update
/// \param ns: namespace
/// \param current_constraints: a vector of string constraints
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
/// \param accu: a vector to which symbols and constant arrays contained in the
///   expression will be appended
static void get_sub_arrays(const exprt &array_expr, std::vector<exprt> &accu)
{
  if(array_expr.id()==ID_if)
  {
    get_sub_arrays(to_if_expr(array_expr).true_case(), accu);
    get_sub_arrays(to_if_expr(array_expr).false_case(), accu);
  }
  else
  {
    if(array_expr.type().id() == ID_array)
    {
      // TODO: check_that it does not contain any sub_array
      accu.push_back(array_expr);
    }
    else
    {
      for(const auto &operand : array_expr.operands())
        get_sub_arrays(operand, accu);
    }
  }
}

/// Add `i` to the index set all the indices that appear in the formula.
/// \param index_set: set of indexes
/// \param ns: namespace
/// \param s: an expression containing strings
/// \param i: an expression representing an index
static void add_to_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const exprt &s,
  exprt i)
{
  simplify(i, ns);
  const bool is_size_t = numeric_cast<std::size_t>(i).has_value();
  if(i.id()!=ID_constant || is_size_t)
  {
    std::vector<exprt> sub_arrays;
    get_sub_arrays(s, sub_arrays);
    for(const auto &sub : sub_arrays)
      if(index_set.cumulative[sub].insert(i).second)
        index_set.current[sub].insert(i);
  }
}

/// Given an array access of the form \a s[i] assumed to be part of a formula
/// \f$ \forall q < u. charconstraint \f$, initialize the index set of \a s
/// so that:
///   - \f$ i[q -> u - 1] \f$ appears in the index set of \a s if \a s is a
///     symbol
///   - if \a s is an array expression, all index from \a 0 to
///     \f$ s.length - 1 \f$ are in the index set
///   - if \a s is an if expression we apply this procedure to the true and
///     false cases
/// \param index_set: the index_set to initialize
/// \param ns: namespace, used for simplifying indexes
/// \param qvar: the quantified variable \a q
/// \param upper_bound: bound \a u on the quantified variable
/// \param s: expression representing a string
/// \param i: expression representing the index at which \a s is accessed
static void initial_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const exprt &qvar,
  const exprt &upper_bound,
  const exprt &s,
  const exprt &i)
{
  PRECONDITION(s.id() == ID_symbol || s.id() == ID_array || s.id() == ID_if);
  if(s.id() == ID_array)
  {
    for(std::size_t j = 0; j < s.operands().size(); ++j)
      add_to_index_set(index_set, ns, s, from_integer(j, i.type()));
    return;
  }
  if(auto ite = expr_try_dynamic_cast<if_exprt>(s))
  {
    initial_index_set(index_set, ns, qvar, upper_bound, ite->true_case(), i);
    initial_index_set(index_set, ns, qvar, upper_bound, ite->false_case(), i);
    return;
  }
  const minus_exprt u_minus_1(upper_bound, from_integer(1, upper_bound.type()));
  exprt i_copy = i;
  replace_expr(qvar, u_minus_1, i_copy);
  add_to_index_set(index_set, ns, s, i_copy);
}

static void initial_index_set(
  index_set_pairt &index_set,
  const namespacet &ns,
  const string_constraintt &axiom)
{
  const symbol_exprt &qvar = axiom.univ_var;
  const auto &bound = axiom.upper_bound;
  auto it = axiom.body.depth_begin();
  const auto end = axiom.body.depth_end();
  while(it != end)
  {
    if(it->id() == ID_index && is_char_type(it->type()))
    {
      const auto &index_expr = to_index_expr(*it);
      const auto &s = index_expr.array();
      initial_index_set(index_set, ns, qvar, bound, s, index_expr.index());
      it.next_sibling_or_parent();
    }
    else
      ++it;
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
    if(it->id() == ID_index && is_char_type(it->type()))
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

/// Add to the index set all the indices that appear in the formula
/// \param index_set: set of indexes
/// \param ns: namespace
/// \param formula: a string constraint
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
    if(cur.id() == ID_index && is_char_type(cur.type()))
    {
      const exprt &s=cur.op0();
      const exprt &i=cur.op1();
      DATA_INVARIANT(
        s.type().id()==ID_array,
        string_refinement_invariantt("index expressions must index on arrays"));
      exprt simplified=simplify_sum(i);
      if(s.id() != ID_array) // do not update index set of constant arrays
        add_to_index_set(index_set, ns, s, simplified);
    }
    else
    {
      forall_operands(it, cur)
        to_process.push_back(*it);
    }
  }
}

/// Find indexes of `str` used in `expr` that contains `qvar`, for instance
/// with arguments ``(str[k+1]=='a')``, `str`, and `k`, the function should
/// return `k+1`.
/// \param [in] expr: the expression to search
/// \param [in] str: the string which must be indexed
/// \param [in] qvar: the universal variable that must be in the index
/// \return index expressions in `expr` on `str` containing `qvar`.
static std::unordered_set<exprt, irep_hash>
find_indexes(const exprt &expr, const exprt &str, const symbol_exprt &qvar)
{
  decltype(find_indexes(expr, str, qvar)) result;
  auto index_str_containing_qvar = [&](const exprt &e) {
    if(auto index_expr = expr_try_dynamic_cast<index_exprt>(e))
    {
      const auto &arr = index_expr->array();
      const auto str_it = std::find(arr.depth_begin(), arr.depth_end(), str);
      return str_it != arr.depth_end() && find_qvar(index_expr->index(), qvar);
    }
    return false;
  };

  std::for_each(expr.depth_begin(), expr.depth_end(), [&](const exprt &e) {
    if(index_str_containing_qvar(e))
      result.insert(to_index_expr(e).index());
  });
  return result;
}

/// Instantiates a string constraint by substituting the quantifiers.
/// For a string constraint of the form `forall q. P(x)`,
/// substitute `q` the universally quantified variable of `axiom`, by
/// an `index`, in `axiom`, so that the index used for `str` equals `val`.
/// For instance, if `axiom` is `forall q. s[q+x] = 'a' && t[q] = 'b'`,
/// `instantiate(axiom,s,v)` would return the expression
/// `s[v] = 'a' && t[v-x] = 'b'`.
/// If there are several such indexes, the conjunction of the instantiations is
/// returned, for instance for a formula:
/// `forall q. s[q+x]='a' && s[q]=c` we would get
/// `s[v] = 'a' && s[v-x] = c && s[v+x] = 'a' && s[v] = c`.
/// \param axiom: a universally quantified formula
/// \param str: an array of characters
/// \param val: an index expression
/// \return instantiated formula
static exprt instantiate(
  const string_constraintt &axiom,
  const exprt &str,
  const exprt &val)
{
  exprt::operandst conjuncts;
  for(const auto &index : find_indexes(axiom.body, str, axiom.univ_var))
  {
    const exprt univ_var_value =
      compute_inverse_function(axiom.univ_var, val, index);
    implies_exprt instance(
      and_exprt(
        binary_relation_exprt(axiom.univ_var, ID_ge, axiom.lower_bound),
        binary_relation_exprt(axiom.univ_var, ID_lt, axiom.upper_bound)),
      axiom.body);
    replace_expr(axiom.univ_var, univ_var_value, instance);
    conjuncts.push_back(instance);
  }
  return conjunction(conjuncts);
}

/// Instantiates a quantified formula representing `not_contains` by
/// substituting the quantifiers and generating axioms.
///
/// For a formula of the form
/// \f$\phi = \forall x. P(x) \Rightarrow Q(x, f(x))\f$
/// let \f$instantiate\_not\_contains(\phi) = ( (f(t) = u) \land
/// P(t) ) \Rightarrow Q(t, u)\f$.
/// Then \f$\forall x.\ P(x) \Rightarrow Q(x, f(x)) \models \f$
/// Axioms of the form \f$\forall x. P(x) \Rightarrow \exists y .Q(x, y) \f$
/// can be transformed into the the equisatisfiable
/// formula \f$\forall x. P(x) \Rightarrow Q(x, f(x))\f$ for a new function
/// symbol `f`. Hence, after transforming axioms of the second type and
/// by the above lemmas, we can create quantifier free formulas that are
/// entailed by a (transformed) axiom.
/// \param [in] axiom: the axiom to instantiate
/// \param index_set: set of indexes
/// \param generator: constraint generator object
/// \return the lemmas produced through instantiation
static std::vector<exprt> instantiate(
  const string_not_contains_constraintt &axiom,
  const index_set_pairt &index_set,
  const string_constraint_generatort &generator,
  const std::map<string_not_contains_constraintt, symbol_exprt> &witnesses)
{
  const array_string_exprt &s0 = axiom.s0();
  const array_string_exprt &s1 = axiom.s1();

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

    return ::instantiate_not_contains(axiom, index_pairs, witnesses);
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
    operand = substitute_array_lists(operand, string_max_length);

  if(expr.id() == ID_array_list)
  {
    DATA_INVARIANT(
      expr.operands().size()>=2,
      string_refinement_invariantt("array-lists must have at least two "
        "operands"));
    const typet &char_type = expr.operands()[1].type();
    array_typet arr_type(char_type, infinity_exprt(char_type));
    exprt ret_expr=array_of_exprt(from_integer(0, char_type), arr_type);

    for(size_t i=0; i<expr.operands().size(); i+=2)
    {
      const exprt &index=expr.operands()[i];
      const exprt &value=expr.operands()[i+1];
      const auto index_value = numeric_cast<std::size_t>(index);
      if(!index.is_constant() ||
         (index_value && *index_value<string_max_length))
        ret_expr=with_exprt(ret_expr, index, value);
    }
    return ret_expr;
  }

  return expr;
}

/// Evaluates the given expression in the valuation found by
/// string_refinementt::dec_solve.
///
/// Arrays of characters are interpreted differently from the result of
/// supert::get: values are propagated to the left to fill unknown.
/// \param expr: an expression
/// \return evaluated expression
exprt string_refinementt::get(const exprt &expr) const
{
  const auto super_get = [this](const exprt &expr) {
    return supert::get(expr);
  };
  exprt ecopy(expr);
  (void)symbol_resolve.replace_expr(ecopy);

  // Special treatment for index expressions
  const auto &index_expr = expr_try_dynamic_cast<index_exprt>(ecopy);
  if(index_expr && is_char_type(index_expr->type()))
  {
    std::reference_wrapper<const exprt> current(index_expr->array());
    while(current.get().id() == ID_if)
    {
      const auto &if_expr = expr_dynamic_cast<if_exprt>(current.get());
      const exprt cond = get(if_expr.cond());
      if(cond.is_true())
        current = std::cref(if_expr.true_case());
      else if(cond.is_false())
        current = std::cref(if_expr.false_case());
      else
        UNREACHABLE;
    }
    const auto array = supert::get(current.get());
    const auto index = get(index_expr->index());
    const exprt unknown =
      from_integer(CHARACTER_FOR_UNKNOWN, index_expr->type());
    if(
      const auto sparse_array = interval_sparse_arrayt::of_expr(array, unknown))
    {
      if(const auto index_value = numeric_cast<std::size_t>(index))
        return sparse_array->at(*index_value);
      return sparse_array->to_if_expression(index);
    }

    INVARIANT(
      array.is_nil() || array.id() == ID_symbol,
      std::string(
        "apart from symbols, array valuations can be interpreted as "
        "sparse arrays, id: ") +
      id2string(array.id()));
    return index_exprt(array, index);
  }

  if(is_char_array_type(ecopy.type(), ns))
  {
    array_string_exprt &arr = to_array_string_expr(ecopy);
    arr.length() = generator.array_pool.get_length(arr);

    if(
      const auto from_dependencies =
        dependencies.eval(arr, [&](const exprt &expr) { return get(expr); }))
      return *from_dependencies;

    if(
      const auto arr_model_opt =
        get_array(super_get, ns, debug(), arr))
      return *arr_model_opt;

    if(generator.array_pool.created_strings().count(arr))
    {
      const exprt length = super_get(arr.length());
      if(const auto n = numeric_cast<std::size_t>(length))
      {
        const interval_sparse_arrayt sparse_array(
          from_integer(CHARACTER_FOR_UNKNOWN, arr.type().subtype()));
        return sparse_array.concretize(*n, length.type());
      }
    }
    return arr;
  }
  return supert::get(ecopy);
}

/// Creates a solver with `axiom` as the only formula added and runs it. If it
/// is SAT, then true is returned and the given evaluation of `var` is stored
/// in `witness`. If UNSAT, then what witness is is undefined.
/// \param ns: namespace
/// \param [in] axiom: the axiom to be checked
/// \param [in] var: the variable whose evaluation will be stored in witness
/// \return: the witness of the satisfying assignment if one
/// exists. If UNSAT, then behaviour is undefined.
static optionalt<exprt> find_counter_example(
  const namespacet &ns,
  const exprt &axiom,
  const symbol_exprt &var)
{
  satcheck_no_simplifiert sat_check;
  boolbvt solver(ns, sat_check);
  solver << axiom;

  if(solver()==decision_proceduret::resultt::D_SATISFIABLE)
    return solver.get(var);
  else
    return { };
}

/// \related string_constraintt
typedef std::map<exprt, std::vector<exprt>> array_index_mapt;

/// \related string_constraintt
static array_index_mapt gather_indices(const exprt &expr)
{
  array_index_mapt indices;
  // clang-format off
  std::for_each(
    expr.depth_begin(),
    expr.depth_end(),
    [&](const exprt &expr)
    {
      const auto index_expr = expr_try_dynamic_cast<const index_exprt>(expr);
      if(index_expr)
        indices[index_expr->array()].push_back(index_expr->index());
    });
  // clang-format on
  return indices;
}

/// \param expr: an expression
/// \param var: a symbol
/// \return Boolean telling whether `expr` is a linear function of `var`.
/// \todo Add unit tests
/// \related string_constraintt
static bool
is_linear_arithmetic_expr(const exprt &expr, const symbol_exprt &var)
{
  for(auto it = expr.depth_begin(); it != expr.depth_end();)
  {
    if(
      it->id() != ID_plus && it->id() != ID_minus &&
      it->id() != ID_unary_minus && *it != var)
    {
      if(find_qvar(*it, var))
        return false;
      else
        it.next_sibling_or_parent();
    }
    else
      ++it;
  }
  return true;
}

/// The universally quantified variable is only allowed to occur in index
/// expressions in the body of a string constraint. This function returns true
/// if this is the case and false otherwise.
/// \related string_constraintt
/// \param [in] expr: The string constraint to check
/// \return true if the universal variable only occurs in index expressions,
///   false otherwise.
static bool universal_only_in_index(const string_constraintt &constr)
{
  for(auto it = constr.body.depth_begin(); it != constr.body.depth_end();)
  {
    if(*it == constr.univ_var)
      return false;
    if(it->id() == ID_index)
      it.next_sibling_or_parent();
    else
      ++it;
  }
  return true;
}

/// Checks the data invariant for \link string_constraintt \endlink
/// \related string_constraintt
/// \param stream: message stream
/// \param ns: namespace
/// \param [in] constraint: the string constraint to check
/// \return whether the constraint satisfies the invariant
static bool is_valid_string_constraint(
  messaget::mstreamt &stream,
  const namespacet &ns,
  const string_constraintt &constraint)
{
  const auto eom=messaget::eom;
  const array_index_mapt body_indices = gather_indices(constraint.body);
  // Must validate for each string. Note that we have an invariant that the
  // second value in the pair is non-empty.
  for(const auto &pair : body_indices)
  {
    // Condition 1: All indices of the same string must be the of the same form
    const exprt rep=pair.second.back();
    for(size_t j=0; j<pair.second.size()-1; j++)
    {
      const exprt i=pair.second[j];
      const equal_exprt equals(rep, i);
      const exprt result=simplify_expr(equals, ns);
      if(result.is_false())
      {
        stream << "Indices not equal: " << to_string(constraint)
               << ", str: " << format(pair.first) << eom;
        return false;
      }
    }

    // Condition 2: f must be linear in the quantified variable
    if(!is_linear_arithmetic_expr(rep, constraint.univ_var))
    {
      stream << "f is not linear: " << to_string(constraint)
             << ", str: " << format(pair.first) << eom;
      return false;
    }

    // Condition 3: the quantified variable can only occur in indices in the
    // body
    if(!universal_only_in_index(constraint))
    {
      stream << "Universal variable outside of index:" << to_string(constraint)
             << eom;
      return false;
    }
  }

  return true;
}

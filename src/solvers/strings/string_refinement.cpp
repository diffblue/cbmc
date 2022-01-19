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

#include "string_refinement.h"

#include <solvers/sat/satcheck.h>
#include <stack>
#include <unordered_set>

#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/format_type.h>
#include <util/magic.h>
#include <util/range.h>
#include <util/simplify_expr.h>

#include "equation_symbol_mapping.h"
#include "string_constraint_instantiation.h"
#include "string_dependencies.h"
#include "string_refinement_invariant.h"

static bool is_valid_string_constraint(
  messaget::mstreamt &stream,
  const namespacet &ns,
  const string_constraintt &constraint);

static optionalt<exprt> find_counter_example(
  const namespacet &ns,
  const exprt &axiom,
  const symbol_exprt &var,
  message_handlert &message_handler);

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
/// \return `true` if the current model satisfies all the axioms, `false`
///   otherwise with a list of lemmas which are obtained by instantiating
///   constraints at indexes given by counter-examples.
static std::pair<bool, std::vector<exprt>> check_axioms(
  const string_axiomst &axioms,
  string_constraint_generatort &generator,
  const std::function<exprt(const exprt &)> &get,
  messaget::mstreamt &stream,
  const namespacet &ns,
  bool use_counter_example,
  const union_find_replacet &symbol_resolve,
  const std::unordered_map<string_not_contains_constraintt, symbol_exprt>
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

static std::vector<exprt> instantiate(
  const string_not_contains_constraintt &axiom,
  const index_set_pairt &index_set,
  const std::unordered_map<string_not_contains_constraintt, symbol_exprt>
    &witnesses);

static optionalt<exprt> get_array(
  const std::function<exprt(const exprt &)> &super_get,
  const namespacet &ns,
  messaget::mstreamt &stream,
  const array_string_exprt &arr,
  const array_poolt &array_pool);

static optionalt<exprt> substitute_array_access(
  const index_exprt &index_expr,
  symbol_generatort &symbol_generator,
  const bool left_propagate);

/// Convert index-value map to a vector of values. If a value for an
/// index is not defined, set it to the value referenced by the next higher
/// index.
/// The length of the resulting vector is the key of the map's
/// last element + 1
/// \param index_value: map containing values of specific vector cells
/// \return Vector containing values as described in the map
template <typename T>
static std::vector<T>
fill_in_map_as_vector(const std::map<std::size_t, T> &index_value)
{
  std::vector<T> result;
  if(!index_value.empty())
  {
    result.resize(index_value.rbegin()->first + 1);
    for(auto it = index_value.rbegin(); it != index_value.rend(); ++it)
    {
      const std::size_t index = it->first;
      const T &value = it->second;
      const auto next = std::next(it);
      const std::size_t leftmost_index_to_pad =
        next != index_value.rend() ? next->first + 1 : 0;
      for(std::size_t j = leftmost_index_to_pad; j <= index; j++)
        result[j] = value;
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

string_refinementt::string_refinementt(const infot &info)
  : string_refinementt(info, validate(info))
{
}

/// Write index set to the given stream, use for debugging
static void
display_index_set(messaget::mstreamt &stream, const index_set_pairt &index_set)
{
  std::size_t count = 0;
  std::size_t count_current = 0;
  for(const auto &i : index_set.cumulative)
  {
    const exprt &s = i.first;
    stream << "IS(" << format(s) << ")=={" << messaget::eom;

    for(const auto &j : i.second)
    {
      const auto it = index_set.current.find(i.first);
      if(
        it != index_set.current.end() && it->second.find(j) != it->second.end())
      {
        count_current++;
        stream << "**";
      }
      stream << "  " << format(j) << ";" << messaget::eom;
      count++;
    }
    stream << "}" << messaget::eom;
  }
  stream << count << " elements in index set (" << count_current
         << " newly added)" << messaget::eom;
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
///     (See <tt>instantiate(messaget::mstreamt&, const string_constraintt&,
///      const exprt &, const exprt&)</tt> for details.)
///   * For formulas of the form
///     \f$\forall x. P(x) \Rightarrow \exists y .s_0[x+y] \ne s_1[y]) \f$ we
///     need to look at the index set of both `s_0` and `s_1`.
///     (See <tt>instantiate(const string_not_contains_constraintt&,
///      const index_set_pairt&,
///      const std::map<string_not_contains_constraintt, symbol_exprt>&)</tt>
///      for details.)
static std::vector<exprt> generate_instantiations(
  const index_set_pairt &index_set,
  const string_axiomst &axioms,
  const std::unordered_map<string_not_contains_constraintt, symbol_exprt>
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
        instantiate(nc_axiom, index_set, not_contain_witnesses))
      lemmas.push_back(instance);
  }
  return lemmas;
}

/// If \p expr is an equation whose right-hand-side is a
/// associate_array_to_pointer call, add the correspondence and replace the call
/// by an expression representing its result.
static void make_char_array_pointer_associations(
  string_constraint_generatort &generator,
  exprt &expr)
{
  if(const auto equal_expr = expr_try_dynamic_cast<equal_exprt>(expr))
  {
    if(
      const auto fun_app = expr_try_dynamic_cast<function_application_exprt>(
        as_const(equal_expr->rhs())))
    {
      const auto new_equation =
        generator.make_array_pointer_association(equal_expr->lhs(), *fun_app);
      if(new_equation)
      {
        expr =
          equal_exprt{from_integer(true, new_equation->type()), *new_equation};
      }
    }
  }
}

/// Substitute sub-expressions in equation by representative elements of
/// `symbol_resolve` whenever possible.
/// Similar to `symbol_resolve.replace_expr` but doesn't mutate the expression
/// and returns the transformed expression instead.
static exprt
replace_expr_copy(const union_find_replacet &symbol_resolve, exprt expr)
{
  symbol_resolve.replace_expr(expr);
  return expr;
}

/// Record the constraints to ensure that the expression is true when
/// the boolean is true and false otherwise.
/// \param expr: an expression of type `bool`
/// \param value: the boolean value to set it to
void string_refinementt::set_to(const exprt &expr, bool value)
{
  PRECONDITION(expr.type().id() == ID_bool);
  PRECONDITION(equality_propagation);
  if(!value)
    equations.push_back(not_exprt{expr});
  else
    equations.push_back(expr);
}

/// Add association for each char pointer in the equation
/// \param symbol_solver: a union_find_replacet object to keep track of
///   char pointer equations
/// \param equations: vector of equations
/// \param ns: namespace
/// \param stream: output stream
/// \return union_find_replacet where char pointer that have been set equal
///   by an equation are associated to the same element
static void add_equations_for_symbol_resolution(
  union_find_replacet &symbol_solver,
  const std::vector<exprt> &equations,
  const namespacet &ns,
  messaget::mstreamt &stream)
{
  const std::string log_message =
    "WARNING string_refinement.cpp generate_symbol_resolution_from_equations:";
  auto equalities = make_range(equations).filter(
    [&](const exprt &e) { return can_cast_expr<equal_exprt>(e); });
  for(const exprt &e : equalities)
  {
    const equal_exprt &eq = to_equal_expr(e);
    const exprt &lhs = to_equal_expr(eq).lhs();
    const exprt &rhs = to_equal_expr(eq).rhs();
    if(lhs.id() != ID_symbol)
    {
      stream << log_message << "non symbol lhs: " << format(lhs)
             << " with rhs: " << format(rhs) << messaget::eom;
      continue;
    }

    if(lhs.type() != rhs.type())
    {
      stream << log_message << "non equal types lhs: " << format(lhs)
             << "\n####################### rhs: " << format(rhs)
             << messaget::eom;
      continue;
    }

    if(is_char_pointer_type(rhs.type()))
    {
      symbol_solver.make_union(lhs, simplify_expr(rhs, ns));
    }
    else if(rhs.id() == ID_function_application)
    {
      // function applications can be ignored because they will be replaced
      // in the convert_function_application step of dec_solve
    }
    else if(
      lhs.type().id() != ID_pointer && has_char_pointer_subtype(lhs.type(), ns))
    {
      if(rhs.type().id() == ID_struct || rhs.type().id() == ID_struct_tag)
      {
        const struct_typet &struct_type = to_struct_type(ns.follow(rhs.type()));
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
               << format(rhs) << "\n  * of type " << format(rhs.type())
               << messaget::eom;
      }
    }
  }
}

/// This is meant to be used on the lhs of an equation with string subtype.
/// \param lhs: expression which is either of string type, or a symbol
///   representing a struct with some string members
/// \param ns: namespace to resolve type tags
/// \return if lhs is a string return this string, if it is a struct return the
///   members of the expression that have string type.
static std::vector<exprt>
extract_strings_from_lhs(const exprt &lhs, const namespacet &ns)
{
  std::vector<exprt> result;
  if(lhs.type() == string_typet())
    result.push_back(lhs);
  else if(lhs.type().id() == ID_struct || lhs.type().id() == ID_struct_tag)
  {
    const struct_typet &struct_type = to_struct_type(ns.follow(lhs.type()));
    for(const auto &comp : struct_type.components())
    {
      const std::vector<exprt> strings_in_comp = extract_strings_from_lhs(
        member_exprt(lhs, comp.get_name(), comp.type()), ns);
      result.insert(
        result.end(), strings_in_comp.begin(), strings_in_comp.end());
    }
  }
  return result;
}

/// \param expr: an expression
/// \param ns: namespace to resolve type tags
/// \return all subexpressions of type string which are not if_exprt expressions
///   this includes expressions of the form `e.x` if e is a symbol subexpression
///   with a field `x` of type string
static std::vector<exprt>
extract_strings(const exprt &expr, const namespacet &ns)
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
      for(const exprt &e : extract_strings_from_lhs(*it, ns))
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
    symbol_resolve.make_union(eq.lhs(), simplify_expr(eq.rhs(), ns));
  }
  else if(has_subtype(eq.lhs().type(), ID_string, ns))
  {
    if(
      eq.rhs().type().id() == ID_struct ||
      eq.rhs().type().id() == ID_struct_tag)
    {
      const struct_typet &struct_type =
        to_struct_type(ns.follow(eq.rhs().type()));
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
  const std::vector<equal_exprt> &equations,
  const namespacet &ns,
  messaget::mstreamt &stream)
{
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

      std::vector<exprt> rhs_strings = extract_strings(eq.rhs(), ns);
      for(const auto &expr : rhs_strings)
        equation_map.add(i, expr);
    }
    else if(
      eq.lhs().type().id() != ID_pointer &&
      has_subtype(eq.lhs().type(), ID_string, ns))
    {
      std::vector<exprt> lhs_strings = extract_strings_from_lhs(eq.lhs(), ns);

      for(const auto &expr : lhs_strings)
        equation_map.add(i, expr);

      if(lhs_strings.empty())
      {
        stream << log_message << "non struct with string subtype "
               << format(eq.lhs()) << "\n  * of type "
               << format(eq.lhs().type()) << messaget::eom;
      }

      for(const exprt &expr : extract_strings(eq.rhs(), ns))
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
static void
output_equations(std::ostream &output, const std::vector<exprt> &equations)
{
  for(std::size_t i = 0; i < equations.size(); ++i)
    output << "  [" << i << "] " << format(equations[i]) << std::endl;
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
  log.debug() << "dec_solve: Initial set of equations" << messaget::eom;
  output_equations(log.debug(), equations);
#endif

  log.debug() << "dec_solve: Build symbol solver from equations"
              << messaget::eom;
  // symbol_resolve is used by get and is kept between calls to dec_solve,
  // that's why we use a class member here
  add_equations_for_symbol_resolution(
    symbol_resolve, equations, ns, log.debug());
#ifdef DEBUG
  log.debug() << "symbol resolve:" << messaget::eom;
  for(const auto &pair : symbol_resolve.to_vector())
    log.debug() << format(pair.first) << " --> " << format(pair.second)
                << messaget::eom;
#endif

  const union_find_replacet string_id_symbol_resolve =
    string_identifiers_resolution_from_equations(
      [&] {
        std::vector<equal_exprt> equalities;
        for(const auto &eq : equations)
        {
          if(auto equal_expr = expr_try_dynamic_cast<equal_exprt>(eq))
            equalities.push_back(*equal_expr);
        }
        return equalities;
      }(),
      ns,
      log.debug());
#ifdef DEBUG
  log.debug() << "symbol resolve string:" << messaget::eom;
  for(const auto &pair : string_id_symbol_resolve.to_vector())
  {
    log.debug() << format(pair.first) << " --> " << format(pair.second)
                << messaget::eom;
  }
#endif

  log.debug() << "dec_solve: Replacing string ids and simplifying arguments"
                 " in function applications"
              << messaget::eom;
  for(exprt &expr : equations)
  {
    auto it = expr.depth_begin();
    while(it != expr.depth_end())
    {
      if(can_cast_expr<function_application_exprt>(*it))
      {
        // Simplification is required because the array pool may not realize
        // that an expression like
        // `(unsignedbv[16]*)((signedbv[8]*)&constarray[0] + 0)` is the
        // same pointer as `&constarray[0]
        simplify(it.mutate(), ns);
        string_id_symbol_resolve.replace_expr(it.mutate());
        it.next_sibling_or_parent();
      }
      else
        ++it;
    }
  }

  // Constraints start clear at each `dec_solve` call.
  string_constraintst constraints;
  for(auto &expr : equations)
    make_char_array_pointer_associations(generator, expr);

#ifdef DEBUG
  output_equations(log.debug(), equations);
#endif

  log.debug() << "dec_solve: compute dependency graph and remove function "
              << "applications captured by the dependencies:" << messaget::eom;
  std::vector<exprt> local_equations;
  for(const exprt &eq : equations)
  {
    // Ensures that arrays that are equal, are associated to the same nodes
    // in the graph.
    const exprt eq_with_char_array_replaced_with_representative_elements =
      replace_expr_copy(symbol_resolve, eq);
    const optionalt<exprt> new_equation = add_node(
      dependencies,
      eq_with_char_array_replaced_with_representative_elements,
      generator.array_pool,
      generator.fresh_symbol);
    if(new_equation)
      local_equations.push_back(*new_equation);
    else
      local_equations.push_back(eq);
  }
  equations.clear();

#ifdef DEBUG
  dependencies.output_dot(log.debug());
#endif

  log.debug() << "dec_solve: add constraints" << messaget::eom;
  merge(constraints, dependencies.add_constraints(generator));

#ifdef DEBUG
  output_equations(log.debug(), equations);
#endif

#ifdef DEBUG
  log.debug() << "dec_solve: arrays_of_pointers:" << messaget::eom;
  for(auto pair : generator.array_pool.get_arrays_of_pointers())
  {
    log.debug() << "  * " << format(pair.first) << "\t--> "
                << format(pair.second) << " : " << format(pair.second.type())
                << messaget::eom;
  }
#endif

  for(const auto &eq : local_equations)
  {
#ifdef DEBUG
    log.debug() << "dec_solve: set_to " << format(eq) << messaget::eom;
#endif
    supert::set_to(eq, true);
  }

  std::transform(
    constraints.universal.begin(),
    constraints.universal.end(),
    std::back_inserter(axioms.universal),
    [&](string_constraintt constraint) {
      constraint.replace_expr(symbol_resolve);
      DATA_INVARIANT(
        is_valid_string_constraint(log.error(), ns, constraint),
        string_refinement_invariantt(
          "string constraints satisfy their invariant"));
      return constraint;
    });

  std::transform(
    constraints.not_contains.begin(),
    constraints.not_contains.end(),
    std::back_inserter(axioms.not_contains),
    [&](string_not_contains_constraintt axiom) {
      replace(symbol_resolve, axiom);
      return axiom;
    });

  // Used to store information about witnesses for not_contains constraints
  std::unordered_map<string_not_contains_constraintt, symbol_exprt>
    not_contain_witnesses;
  for(const auto &nc_axiom : axioms.not_contains)
  {
    const auto &witness_type = [&] {
      const auto &rtype = to_array_type(nc_axiom.s0.type());
      const typet &index_type = rtype.size().type();
      return array_typet(index_type, infinity_exprt(index_type));
    }();
    not_contain_witnesses.emplace(
      nc_axiom, generator.fresh_symbol("not_contains_witness", witness_type));
  }

  for(const exprt &lemma : constraints.existential)
  {
    add_lemma(substitute_array_access(lemma, generator.fresh_symbol, true));
  }

  // All generated strings should have non-negative length
  for(const auto &pair : generator.array_pool.created_strings())
  {
    exprt length = generator.array_pool.get_or_create_length(pair.first);
    add_lemma(
      binary_relation_exprt{length, ID_ge, from_integer(0, length.type())});
  }

  // Initial try without index set
  const auto get = [this](const exprt &expr) { return this->get(expr); };
  dependencies.clean_cache();
  const decision_proceduret::resultt initial_result = supert::dec_solve();
  if(initial_result == resultt::D_SATISFIABLE)
  {
    bool satisfied;
    std::vector<exprt> counter_examples;
    std::tie(satisfied, counter_examples) = check_axioms(
      axioms,
      generator,
      get,
      log.debug(),
      ns,
      config_.use_counter_example,
      symbol_resolve,
      not_contain_witnesses);
    if(satisfied)
    {
      log.debug() << "check_SAT: the model is correct" << messaget::eom;
      return resultt::D_SATISFIABLE;
    }
    log.debug() << "check_SAT: got SAT but the model is not correct"
                << messaget::eom;
  }
  else
  {
    log.debug() << "check_SAT: got UNSAT or ERROR" << messaget::eom;
    return initial_result;
  }

  initial_index_set(index_sets, ns, axioms);
  update_index_set(index_sets, ns, current_constraints);
  current_constraints.clear();
  const auto initial_instances =
    generate_instantiations(index_sets, axioms, not_contain_witnesses);
  for(const auto &instance : initial_instances)
  {
    add_lemma(substitute_array_access(instance, generator.fresh_symbol, true));
  }

  while((loop_bound_--) > 0)
  {
    dependencies.clean_cache();
    const decision_proceduret::resultt refined_result = supert::dec_solve();

    if(refined_result == resultt::D_SATISFIABLE)
    {
      bool satisfied;
      std::vector<exprt> counter_examples;
      std::tie(satisfied, counter_examples) = check_axioms(
        axioms,
        generator,
        get,
        log.debug(),
        ns,
        config_.use_counter_example,
        symbol_resolve,
        not_contain_witnesses);
      if(satisfied)
      {
        log.debug() << "check_SAT: the model is correct" << messaget::eom;
        return resultt::D_SATISFIABLE;
      }

      log.debug()
        << "check_SAT: got SAT but the model is not correct, refining..."
        << messaget::eom;

      // Since the model is not correct although we got SAT, we need to refine
      // the property we are checking by adding more indices to the index set,
      // and instantiating universal formulas with this indices.
      // We will then relaunch the solver with these added lemmas.
      index_sets.current.clear();
      update_index_set(index_sets, ns, current_constraints);

      display_index_set(log.debug(), index_sets);

      if(index_sets.current.empty())
      {
        if(axioms.not_contains.empty())
        {
          log.error() << "dec_solve: current index set is empty, "
                      << "this should not happen" << messaget::eom;
          return resultt::D_ERROR;
        }
        else
        {
          log.debug() << "dec_solve: current index set is empty, "
                      << "adding counter examples" << messaget::eom;
          for(const auto &counter : counter_examples)
            add_lemma(counter);
        }
      }
      current_constraints.clear();
      const auto instances =
        generate_instantiations(index_sets, axioms, not_contain_witnesses);
      for(const auto &instance : instances)
        add_lemma(
          substitute_array_access(instance, generator.fresh_symbol, true));
    }
    else
    {
      log.debug() << "check_SAT: default return "
                  << static_cast<int>(refined_result) << messaget::eom;
      return refined_result;
    }
  }
  log.debug() << "string_refinementt::dec_solve reached the maximum number"
              << "of steps allowed" << messaget::eom;
  return resultt::D_ERROR;
}
/// Add the given lemma to the solver.
/// \param lemma: a Boolean expression
/// \param simplify_lemma: whether the lemma should be simplified before being
///   given to the underlying solver.
void string_refinementt::add_lemma(
  const exprt &lemma,
  const bool simplify_lemma)
{
  if(!seen_instances.insert(lemma).second)
    return;

  current_constraints.push_back(lemma);

  exprt simple_lemma = lemma;
  if(simplify_lemma)
  {
    simplify(simple_lemma, ns);
  }

  if(simple_lemma.is_true())
  {
#if 0
    log.debug() << "string_refinementt::add_lemma : tautology" << messaget::eom;
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
        from_integer(
          CHARACTER_FOR_UNKNOWN, to_array_type(it->type()).subtype()),
        to_array_type(it->type()));
      it.next_sibling_or_parent();
    }
    else
      ++it;
  }

  log.debug() << "adding lemma " << format(simple_lemma) << messaget::eom;

  prop.l_set_to_true(convert(simple_lemma));
}

/// Get a model of the size of the input string.
/// First ask the solver for a size value. If the solver has no value, get the
/// size directly from the type. This is the case for string literals that are
/// not part of the decision procedure (e.g. literals in return values).
/// If the size value is not a constant or not a valid integer (size_t),
/// return no value.
/// \param super_get: function returning the valuation of an expression
///   in a model
/// \param ns: namespace
/// \param stream: output stream for warning messages
/// \param arr: expression of type array representing a string
/// \param array_pool: pool of arrays representing strings
/// \return an optional expression representing the size of the array that can
///         be cast to size_t
static optionalt<exprt> get_valid_array_size(
  const std::function<exprt(const exprt &)> &super_get,
  const namespacet &ns,
  messaget::mstreamt &stream,
  const array_string_exprt &arr,
  const array_poolt &array_pool)
{
  const auto &size_from_pool = array_pool.get_length_if_exists(arr);
  exprt size_val;
  if(size_from_pool.has_value())
  {
    const exprt size = size_from_pool.value();
    size_val = simplify_expr(super_get(size), ns);
    if(size_val.id() != ID_constant)
    {
      stream << "(sr::get_valid_array_size) string of unknown size: "
             << format(size_val) << messaget::eom;
      return {};
    }
  }
  else if(to_array_type(arr.type()).size().id() == ID_constant)
    size_val = simplify_expr(to_array_type(arr.type()).size(), ns);
  else
    return {};

  auto n_opt = numeric_cast<std::size_t>(size_val);
  if(!n_opt)
  {
    stream << "(sr::get_valid_array_size) size is not valid" << messaget::eom;
    return {};
  }

  return size_val;
}

/// Get a model of an array and put it in a certain form.
/// If the model is incomplete or if it is too big, return no value.
/// \param super_get: function returning the valuation of an expression
///   in a model
/// \param ns: namespace
/// \param stream: output stream for warning messages
/// \param arr: expression of type array representing a string
/// \param array_pool: pool of arrays representing strings
/// \return an optional array expression or array_of_exprt
static optionalt<exprt> get_array(
  const std::function<exprt(const exprt &)> &super_get,
  const namespacet &ns,
  messaget::mstreamt &stream,
  const array_string_exprt &arr,
  const array_poolt &array_pool)
{
  const auto size =
    get_valid_array_size(super_get, ns, stream, arr, array_pool);
  if(!size.has_value())
  {
    return {};
  }

  const size_t n = numeric_cast<std::size_t>(size.value()).value();

  if(n > MAX_CONCRETE_STRING_SIZE)
  {
    stream << "(sr::get_valid_array_size) long string (size "
           << " = " << n << ") " << format(arr) << messaget::eom;
    stream << "(sr::get_valid_array_size) consider reducing "
              "max-nondet-string-length so "
              "that no string exceeds "
           << MAX_CONCRETE_STRING_SIZE
           << " in length and "
              "make sure all functions returning strings are loaded"
           << messaget::eom;
    stream << "(sr::get_valid_array_size) this can also happen on invalid "
              "object access"
           << messaget::eom;
    return nil_exprt();
  }

  const exprt arr_val = simplify_expr(super_get(arr), ns);
  const typet char_type = to_array_type(arr.type()).subtype();
  const typet &index_type = size.value().type();

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
  if(arr.type().id() != ID_array)
    return std::string("");

  exprt size_expr = to_array_type(arr.type()).size();
  auto n = numeric_cast_v<std::size_t>(to_constant_expr(size_expr));
  return utf16_constant_array_to_java(arr, n);
}

/// Debugging function which finds the valuation of the given array in
/// `super_get` and concretize unknown characters.
/// \param super_get: give a valuation to variables
/// \param ns: namespace
/// \param stream: output stream
/// \param arr: array expression
/// \param array_pool: pool of arrays representing strings
/// \return expression corresponding to `arr` in the model
static exprt get_char_array_and_concretize(
  const std::function<exprt(const exprt &)> &super_get,
  const namespacet &ns,
  messaget::mstreamt &stream,
  const array_string_exprt &arr,
  array_poolt &array_pool)
{
  stream << "- " << format(arr) << ":\n";
  stream << std::string(4, ' ') << "- type: " << format(arr.type())
         << messaget::eom;
  const auto arr_model_opt = get_array(super_get, ns, stream, arr, array_pool);
  if(arr_model_opt)
  {
    stream << std::string(4, ' ') << "- char_array: " << format(*arr_model_opt)
           << '\n';
    stream << std::string(4, ' ')
           << "- type : " << format(arr_model_opt->type()) << messaget::eom;
    const exprt simple = simplify_expr(*arr_model_opt, ns);
    stream << std::string(4, ' ')
           << "- simplified_char_array: " << format(simple) << messaget::eom;
    if(
      const auto concretized_array = get_array(
        super_get, ns, stream, to_array_string_expr(simple), array_pool))
    {
      stream << std::string(4, ' ')
             << "- concretized_char_array: " << format(*concretized_array)
             << messaget::eom;

      if(
        const auto array_expr =
          expr_try_dynamic_cast<array_exprt>(*concretized_array))
      {
        stream << std::string(4, ' ') << "- as_string: \""
               << string_of_array(*array_expr) << "\"\n";
      }
      else
        stream << std::string(2, ' ') << "- warning: not an array"
               << messaget::eom;
      return *concretized_array;
    }
    return simple;
  }
  stream << std::string(4, ' ') << "- incomplete model" << messaget::eom;
  return arr;
}

/// Display part of the current model by mapping the variables created by the
/// solver to constant expressions given by the current model
void debug_model(
  const string_constraint_generatort &generator,
  messaget::mstreamt &stream,
  const namespacet &ns,
  const std::function<exprt(const exprt &)> &super_get,
  const std::vector<symbol_exprt> &symbols,
  array_poolt &array_pool)
{
  stream << "debug_model:" << '\n';
  for(const auto &pointer_array : generator.array_pool.get_arrays_of_pointers())
  {
    const auto arr = pointer_array.second;
    const exprt model =
      get_char_array_and_concretize(super_get, ns, stream, arr, array_pool);

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
/// \param expr: A (possibly nested) 'with' expression on an `array_of`
///   expression. The function checks that the expression is of the form
///   `with_expr(with_expr(...(array_of(...)))`. This is the form in which
///   array valuations coming from the underlying solver are given.
/// \param index: An index with which to build the equality condition
/// \param left_propagate: If set to true, the expression will look like
///   `index<=0 ? 24 : index<=2 ? 42 : 12`
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
  symbol_generatort &symbol_generator)
{
  const typet &char_type = array_expr.type().element_type();
  const exprt default_val = symbol_generator("out_of_bound_access", char_type);
  const interval_sparse_arrayt sparse_array(array_expr, default_val);
  return sparse_array.to_if_expression(index);
}

static exprt substitute_array_access(
  const if_exprt &if_expr,
  const exprt &index,
  symbol_generatort &symbol_generator,
  const bool left_propagate)
{
  exprt true_index = index_exprt(if_expr.true_case(), index);
  exprt false_index = index_exprt(if_expr.false_case(), index);

  // Substitute recursively in branches of conditional expressions
  optionalt<exprt> substituted_true_case =
    substitute_array_access(true_index, symbol_generator, left_propagate);
  optionalt<exprt> substituted_false_case =
    substitute_array_access(false_index, symbol_generator, left_propagate);

  return if_exprt(
    if_expr.cond(),
    substituted_true_case ? *substituted_true_case : true_index,
    substituted_false_case ? *substituted_false_case : false_index);
}

static optionalt<exprt> substitute_array_access(
  const index_exprt &index_expr,
  symbol_generatort &symbol_generator,
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
    array.is_nil() || array.id() == ID_symbol || array.id() == ID_nondet_symbol,
    std::string(
      "in case the array is unknown, it should be a symbol or nil, id: ") +
      id2string(array.id()));
  return {};
}

/// Auxiliary function for substitute_array_access
/// Performs the same operation but modifies the argument instead of returning
/// the resulting expression.
static void substitute_array_access_in_place(
  exprt &expr,
  symbol_generatort &symbol_generator,
  const bool left_propagate)
{
  // Recurse down structure and modify on the way.
  for(auto it = expr.depth_begin(), itend = expr.depth_end(); it != itend; ++it)
  {
    if(const auto index_expr = expr_try_dynamic_cast<index_exprt>(*it))
    {
      optionalt<exprt> result =
        substitute_array_access(*index_expr, symbol_generator, left_propagate);

      // Only perform a write when we have something changed.
      if(result)
        it.mutate() = *result;
    }
  }
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
/// \param symbol_generator: a symbol generator
/// \param left_propagate: should values be propagated to the left in with
///   expressions
/// \return an expression containing no array access
exprt substitute_array_access(
  exprt expr,
  symbol_generatort &symbol_generator,
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
/// \return the negation of the axiom under the current evaluation
static exprt negation_of_not_contains_constraint(
  const string_not_contains_constraintt &constraint,
  const symbol_exprt &univ_var,
  const std::function<exprt(const exprt &)> &get)
{
  // If the for all is vacuously true, the negation is false.
  const auto lbe = numeric_cast_v<mp_integer>(
    to_constant_expr(get(constraint.exists_lower_bound)));
  const auto ube = numeric_cast_v<mp_integer>(
    to_constant_expr(get(constraint.exists_upper_bound)));
  const auto univ_bounds = and_exprt(
    binary_relation_exprt(get(constraint.univ_lower_bound), ID_le, univ_var),
    binary_relation_exprt(get(constraint.univ_upper_bound), ID_gt, univ_var));

  // The negated existential becomes an universal, and this is the unrolling of
  // that universal quantifier.
  // Ff the upper bound is smaller than the lower bound (specifically, it might
  // actually be negative as it is initially unconstrained) then there is
  // nothing to do (and the reserve call would fail).
  if(ube < lbe)
    return and_exprt(univ_bounds, get(constraint.premise));

  std::vector<exprt> conjuncts;
  conjuncts.reserve(numeric_cast_v<std::size_t>(ube - lbe));
  for(mp_integer i = lbe; i < ube; ++i)
  {
    const constant_exprt i_expr = from_integer(i, univ_var.type());
    const exprt s0_char =
      get(index_exprt(constraint.s0, plus_exprt(univ_var, i_expr)));
    const exprt s1_char = get(index_exprt(constraint.s1, i_expr));
    conjuncts.push_back(equal_exprt(s0_char, s1_char));
  }
  const exprt equal_strings = conjunction(conjuncts);
  return and_exprt(univ_bounds, get(constraint.premise), equal_strings);
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
  stream << '\n'
         << std::string(4, ' ') << "- axiom_in_model:\n"
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
  const std::unordered_map<string_not_contains_constraintt, symbol_exprt>
    &not_contain_witnesses)
{
  stream << "string_refinementt::check_axioms:" << messaget::eom;

  stream << "symbol_resolve:" << messaget::eom;
  auto pairs = symbol_resolve.to_vector();
  for(const auto &pair : pairs)
    stream << "  - " << format(pair.first) << " --> " << format(pair.second)
           << messaget::eom;

#ifdef DEBUG
  debug_model(
    generator,
    stream,
    ns,
    get,
    generator.fresh_symbol.created_symbols,
    generator.array_pool);
#endif

  // Maps from indexes of violated universal axiom to a witness of violation
  std::map<size_t, exprt> violated;

  stream << "string_refinement::check_axioms: " << axioms.universal.size()
         << " universal axioms:" << messaget::eom;
  for(size_t i = 0; i < axioms.universal.size(); i++)
  {
    const string_constraintt &axiom = axioms.universal[i];
    const string_constraintt axiom_in_model(
      axiom.univ_var,
      get(axiom.lower_bound),
      get(axiom.upper_bound),
      get(axiom.body));

    exprt negaxiom = axiom_in_model.negation();
    negaxiom = simplify_expr(negaxiom, ns);

    stream << std::string(2, ' ') << i << ".\n";
    const exprt with_concretized_arrays =
      substitute_array_access(negaxiom, generator.fresh_symbol, true);
    debug_check_axioms_step(
      stream, axiom, axiom_in_model, negaxiom, with_concretized_arrays);

    if(
      const auto &witness = find_counter_example(
        ns,
        with_concretized_arrays,
        axiom.univ_var,
        stream.message.get_message_handler()))
    {
      stream << std::string(4, ' ')
             << "- violated_for: " << format(axiom.univ_var) << "="
             << format(*witness) << messaget::eom;
      violated[i] = *witness;
    }
    else
      stream << std::string(4, ' ') << "- correct" << messaget::eom;
  }

  // Maps from indexes of violated not_contains axiom to a witness of violation
  std::map<std::size_t, exprt> violated_not_contains;

  stream << "there are " << axioms.not_contains.size() << " not_contains axioms"
         << messaget::eom;
  for(std::size_t i = 0; i < axioms.not_contains.size(); i++)
  {
    const string_not_contains_constraintt &nc_axiom = axioms.not_contains[i];
    const symbol_exprt univ_var = generator.fresh_symbol(
      "not_contains_univ_var", nc_axiom.s0.length_type());
    const exprt negated_axiom = negation_of_not_contains_constraint(
      nc_axiom, univ_var, [&](const exprt &expr) {
        return simplify_expr(get(expr), ns);
      });

    stream << std::string(2, ' ') << i << ".\n";
    debug_check_axioms_step(
      stream, nc_axiom, nc_axiom, negated_axiom, negated_axiom);

    if(
      const auto witness = find_counter_example(
        ns, negated_axiom, univ_var, stream.message.get_message_handler()))
    {
      stream << std::string(4, ' ')
             << "- violated_for: " << univ_var.get_identifier() << "="
             << format(*witness) << messaget::eom;
      violated_not_contains[i] = *witness;
    }
  }

  if(violated.empty() && violated_not_contains.empty())
  {
    stream << "no violated property" << messaget::eom;
    return {true, std::vector<exprt>()};
  }
  else
  {
    stream << violated.size() << " universal string axioms can be violated"
           << messaget::eom;
    stream << violated_not_contains.size()
           << " not_contains string axioms can be violated" << messaget::eom;

    if(use_counter_example)
    {
      std::vector<exprt> lemmas;

      for(const auto &v : violated)
      {
        const exprt &val = v.second;
        const string_constraintt &axiom = axioms.universal[v.first];

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
        const exprt &val = v.second;
        const string_not_contains_constraintt &axiom =
          axioms.not_contains[v.first];

        const exprt func_val =
          index_exprt(not_contain_witnesses.at(axiom), val);
        const exprt comp_val = simplify_sum(plus_exprt(val, func_val));

        std::set<std::pair<exprt, exprt>> indices;
        indices.insert(std::pair<exprt, exprt>(comp_val, func_val));
        const exprt counter =
          ::instantiate_not_contains(axiom, indices, not_contain_witnesses)[0];
        lemmas.push_back(counter);
      }
      return {false, lemmas};
    }
  }
  return {false, std::vector<exprt>()};
}

/// \param f: an expression with only plus and minus expr
/// \return an equivalent expression in a canonical form
exprt simplify_sum(const exprt &f)
{
  return linear_functiont{f}.to_expr();
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
/// \param array_expr: an expression representing an array
/// \param accu: a vector to which symbols and constant arrays contained in the
///   expression will be appended
static void get_sub_arrays(const exprt &array_expr, std::vector<exprt> &accu)
{
  if(array_expr.id() == ID_if)
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
  if(i.id() != ID_constant || is_size_t)
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
  PRECONDITION(
    s.id() == ID_symbol || s.id() == ID_nondet_symbol || s.id() == ID_array ||
    s.id() == ID_if);
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
  auto it = axiom.premise.depth_begin();
  const auto end = axiom.premise.depth_end();
  while(it != end)
  {
    if(it->id() == ID_index && is_char_type(it->type()))
    {
      const exprt &s = to_index_expr(*it).array();
      const exprt &i = to_index_expr(*it).index();

      // cur is of the form s[i] and no quantified variable appears in i
      add_to_index_set(index_set, ns, s, i);

      it.next_sibling_or_parent();
    }
    else
      ++it;
  }

  const minus_exprt kminus1(
    axiom.exists_upper_bound, from_integer(1, axiom.exists_upper_bound.type()));
  add_to_index_set(index_set, ns, axiom.s1.content(), kminus1);
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
    exprt cur = to_process.back();
    to_process.pop_back();
    if(cur.id() == ID_index && is_char_type(cur.type()))
    {
      const exprt &s = to_index_expr(cur).array();
      const exprt &i = to_index_expr(cur).index();
      DATA_INVARIANT(
        s.type().id() == ID_array,
        string_refinement_invariantt("index expressions must index on arrays"));
      exprt simplified = simplify_sum(i);
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
/// \param witnesses: \p axiom's witnesses for non-containment
/// \return the lemmas produced through instantiation
static std::vector<exprt> instantiate(
  const string_not_contains_constraintt &axiom,
  const index_set_pairt &index_set,
  const std::unordered_map<string_not_contains_constraintt, symbol_exprt>
    &witnesses)
{
  const array_string_exprt &s0 = axiom.s0;
  const array_string_exprt &s1 = axiom.s1;

  const auto &index_set0 = index_set.cumulative.find(s0.content());
  const auto &index_set1 = index_set.cumulative.find(s1.content());
  const auto &current_index_set0 = index_set.current.find(s0.content());
  const auto &current_index_set1 = index_set.current.find(s1.content());

  if(
    index_set0 != index_set.cumulative.end() &&
    index_set1 != index_set.cumulative.end() &&
    current_index_set0 != index_set.current.end() &&
    current_index_set1 != index_set.current.end())
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
  return {};
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
      expr.operands().size() >= 2,
      string_refinement_invariantt("array-lists must have at least two "
                                   "operands"));
    const typet &char_type = expr.operands()[1].type();
    array_typet arr_type(char_type, infinity_exprt(char_type));
    exprt ret_expr = array_of_exprt(from_integer(0, char_type), arr_type);

    for(size_t i = 0; i < expr.operands().size(); i += 2)
    {
      const exprt &index = expr.operands()[i];
      const exprt &value = expr.operands()[i + 1];
      const auto index_value = numeric_cast<std::size_t>(index);
      if(
        !index.is_constant() ||
        (index_value && *index_value < string_max_length))
        ret_expr = with_exprt(ret_expr, index, value);
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

    // If the underlying solver does not know about the existence of an array,
    // it can return nil, which cannot be used in the expression returned here.
    if(array.is_nil())
      return index_exprt(current, index);

    const exprt unknown =
      from_integer(CHARACTER_FOR_UNKNOWN, index_expr->type());
    if(
      const auto sparse_array = interval_sparse_arrayt::of_expr(array, unknown))
    {
      if(const auto index_value = numeric_cast<std::size_t>(index))
        return sparse_array->at(*index_value);
      return sparse_array->to_if_expression(index);
    }

    INVARIANT(array.id() == ID_symbol || array.id() == ID_nondet_symbol,
              "Apart from symbols, array valuations can be interpreted as "
              "sparse arrays. Array model : " + array.pretty());
    return index_exprt(array, index);
  }

  if(is_char_array_type(ecopy.type(), ns))
  {
    array_string_exprt &arr = to_array_string_expr(ecopy);

    if(
      const auto from_dependencies =
        dependencies.eval(arr, [&](const exprt &expr) { return get(expr); }))
      return *from_dependencies;

    if(
      const auto arr_model_opt =
        get_array(super_get, ns, log.debug(), arr, generator.array_pool))
      return *arr_model_opt;

    if(
      const auto &length_from_pool =
        generator.array_pool.get_length_if_exists(arr))
    {
      const exprt length = super_get(length_from_pool.value());

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
/// \param message_handler: message handler
/// \return the witness of the satisfying assignment if one
///   exists. If UNSAT, then behaviour is undefined.
static optionalt<exprt> find_counter_example(
  const namespacet &ns,
  const exprt &axiom,
  const symbol_exprt &var,
  message_handlert &message_handler)
{
  satcheck_no_simplifiert sat_check(message_handler);
  boolbvt solver(ns, sat_check, message_handler);
  solver << axiom;

  if(solver() == decision_proceduret::resultt::D_SATISFIABLE)
    return solver.get(var);
  else
    return {};
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
      if(std::find(it->depth_begin(), it->depth_end(), var) != it->depth_end())
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
/// \param [in] constr: The string constraint to check
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
  const array_index_mapt body_indices = gather_indices(constraint.body);
  // Must validate for each string. Note that we have an invariant that the
  // second value in the pair is non-empty.
  for(const auto &pair : body_indices)
  {
    // Condition 1: All indices of the same string must be the of the same form
    const exprt rep = pair.second.back();
    for(size_t j = 0; j < pair.second.size() - 1; j++)
    {
      const exprt i = pair.second[j];
      const equal_exprt equals(rep, i);
      const exprt result = simplify_expr(equals, ns);
      if(result.is_false())
      {
        stream << "Indices not equal: " << to_string(constraint)
               << ", str: " << format(pair.first) << messaget::eom;
        return false;
      }
    }

    // Condition 2: f must be linear in the quantified variable
    if(!is_linear_arithmetic_expr(rep, constraint.univ_var))
    {
      stream << "f is not linear: " << to_string(constraint)
             << ", str: " << format(pair.first) << messaget::eom;
      return false;
    }

    // Condition 3: the quantified variable can only occur in indices in the
    // body
    if(!universal_only_in_index(constraint))
    {
      stream << "Universal variable outside of index:" << to_string(constraint)
             << messaget::eom;
      return false;
    }
  }

  return true;
}

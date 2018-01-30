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
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/refinement/string_constraint_instantiation.h>
#include <java_bytecode/java_types.h>
#include <unordered_set>

static exprt substitute_array_with_expr(const exprt &expr, const exprt &index);

static bool is_valid_string_constraint(
  messaget::mstreamt &stream,
  const namespacet &ns,
  const string_constraintt &expr);

static optionalt<exprt> find_counter_example(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const exprt &axiom,
  const symbol_exprt &var);

/// Check axioms takes the model given by the underlying solver and answers
/// whether it satisfies the string constraints.
///
/// For each string_constraint `a`:
///   * the negation of `a` is an existential formula `b`;
///   * we substituted symbols in `b` by their values found in `get`;
///   * arrays are concretized, meaning we attribute a value for characters that
///     are unknown to get, for details see concretize_arrays_in_expression;
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
  std::size_t max_string_length,
  bool use_counter_example,
  ui_message_handlert::uit ui,
  const union_find_replacet &symbol_resolve);

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
  messaget::mstreamt &stream,
  const string_constraintt &axiom,
  const exprt &str,
  const exprt &val);

static std::vector<exprt> instantiate(
  const string_not_contains_constraintt &axiom,
  const index_set_pairt &index_set,
  const string_constraint_generatort &generator);

static optionalt<exprt> get_array(
  const std::function<exprt(const exprt &)> &super_get,
  const namespacet &ns,
  const std::size_t max_string_length,
  messaget::mstreamt &stream,
  const array_string_exprt &arr);

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

string_refinementt::string_refinementt(const infot &info, bool):
  supert(info),
  config_(info),
  loop_bound_(info.refinement_bound),
  generator(info, *info.ns) { }

string_refinementt::string_refinementt(const infot &info):
  string_refinementt(info, validate(info)) { }

/// display the current index set, for debugging
static void display_index_set(
  messaget::mstreamt &stream,
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
///     (See
// NOLINTNEXTLINE
///     `instantiate(messaget::mstreamt&,const string_constraintt&,const exprt &,const exprt&)`
///      for details)
///   * For formulas of the form
///     \f$\forall x. P(x) \Rightarrow \exists y .s_0[x+y] \ne s_1[y]) \f$ we
///     need to look at the index set of both `s_0` and `s_1`.
///     (See `instantiate(const string_not_contains_constraintt &axiom)`
///      for details)
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

/// Remove functions applications and create the necessary axioms.
/// \param expr: an expression possibly containing function applications
/// \param generator: generator for the string constraints
/// \return an expression containing no function application
static exprt substitute_function_applications(
  exprt expr,
  string_constraint_generatort &generator)
{
  for(auto &operand : expr.operands())
    operand = substitute_function_applications(operand, generator);

  if(expr.id() == ID_function_application)
    return generator.add_axioms_for_function_application(
      to_function_application_expr(expr));

  return expr;
}

/// Remove functions applications and create the necessary axioms.
/// \param equations: vector of equations
/// \param generator: generator for the string constraints
/// \return vector of equations where function application have been replaced
static void substitute_function_applications_in_equations(
  std::vector<equal_exprt> &equations,
  string_constraint_generatort &generator)
{
  for(auto &eq : equations)
    eq.rhs() = substitute_function_applications(eq.rhs(), generator);
}

/// For now, any unsigned bitvector type of width smaller or equal to 16 is
/// considered a character.
/// \note type that are not characters maybe detected as characters (for
/// instance unsigned char in C), this will make dec_solve do unnecessary
/// steps for these, but should not affect correctness.
/// \param type: a type
/// \return true if the given type represents characters
bool is_char_type(const typet &type)
{
  return type.id() == ID_unsignedbv &&
         to_unsignedbv_type(type).get_width() <= 16;
}

/// Distinguish char array from other types.
/// For now, any unsigned bitvector type is considered a character.
/// \param type: a type
/// \param ns: namespace
/// \return true if the given type is an array of characters
bool is_char_array_type(const typet &type, const namespacet &ns)
{
  if(type.id()==ID_symbol)
    return is_char_array_type(ns.follow(type), ns);
  return type.id() == ID_array && is_char_type(type.subtype());
}

/// For now, any unsigned bitvector type is considered a character.
/// \param type: a type
/// \return true if the given type represents a pointer to characters
bool is_char_pointer_type(const typet &type)
{
  return type.id() == ID_pointer && is_char_type(type.subtype());
}

/// \param type: a type
/// \param pred: a predicate
/// \return true if one of the subtype of `type` satisfies predicate `pred`.
///         The meaning of "subtype" is in the algebraic datatype sense:
///         for example, the subtypes of a struct are the types of its
///         components, the subtype of a pointer is the type it points to,
///         etc...
///         For instance in the type `t` defined by
///         `{ int a; char[] b; double * c; { bool d} e}`, `int`, `char`,
///         `double` and `bool` are subtypes of `t`.
bool has_subtype(
  const typet &type,
  const std::function<bool(const typet &)> &pred)
{
  if(pred(type))
    return true;

  if(type.id() == ID_struct || type.id() == ID_union)
  {
    const struct_union_typet &struct_type = to_struct_union_type(type);
    return std::any_of(
      struct_type.components().begin(),
      struct_type.components().end(), // NOLINTNEXTLINE
      [&](const struct_union_typet::componentt &comp) {
        return has_subtype(comp.type(), pred);
      });
  }

  return std::any_of( // NOLINTNEXTLINE
    type.subtypes().begin(), type.subtypes().end(), [&](const typet &t) {
      return has_subtype(t, pred);
    });
}

/// \param type: a type
/// \return true if a subtype of `type` is an pointer of characters.
///         The meaning of "subtype" is in the algebraic datatype sense:
///         for example, the subtypes of a struct are the types of its
///         components, the subtype of a pointer is the type it points to,
///         etc...
static bool has_char_pointer_subtype(const typet &type)
{
  return has_subtype(type, is_char_pointer_type);
}

/// \param type: a type
/// \return true if a subtype of `type` is string_typet.
///         The meaning of "subtype" is in the algebraic datatype sense:
///         for example, the subtypes of a struct are the types of its
///         components, the subtype of a pointer is the type it points to,
///         etc...
static bool has_string_subtype(const typet &type)
{
  // NOLINTNEXTLINE
  return has_subtype(
    type, [](const typet &subtype) { return subtype == string_typet(); });
}

/// \param expr: an expression
/// \param ns: namespace
/// \return true if a subexpression of `expr` is an array of characters
static bool has_char_array_subexpr(const exprt &expr, const namespacet &ns)
{
  for(auto it = expr.depth_begin(); it != expr.depth_end(); ++it)
    if(is_char_array_type(it->type(), ns))
      return true;
  return false;
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
/// \param equations: vector of equations
/// \param ns: namespace
/// \param stream: output stream
/// \return union_find_replacet where char pointer that have been set equal
///         by an equation are associated to the same element
static union_find_replacet generate_symbol_resolution_from_equations(
  const std::vector<equal_exprt> &equations,
  const namespacet &ns,
  messaget::mstreamt &stream)
{
  const auto eom = messaget::eom;
  const std::string log_message =
    "WARNING string_refinement.cpp generate_symbol_resolution_from_equations:";
  union_find_replacet solver;
  for(const equal_exprt &eq : equations)
  {
    const exprt &lhs = eq.lhs();
    const exprt &rhs = eq.rhs();
    if(lhs.id()!=ID_symbol)
    {
      stream << log_message << "non symbol lhs: " << from_expr(ns, "", lhs)
             << " with rhs: " << from_expr(ns, "", rhs) << eom;
      continue;
    }

    if(lhs.type()!=rhs.type())
    {
      stream << log_message << "non equal types lhs: " << from_expr(ns, "", lhs)
             << "\n####################### rhs: " << from_expr(ns, "", rhs)
             << eom;
      continue;
    }

    if(is_char_pointer_type(rhs.type()))
    {
      solver.make_union(lhs, rhs);
    }
    else if(rhs.id() == ID_function_application)
    {
      // function applications can be ignored because they will be replaced
      // in the convert_function_application step of dec_solve
    }
    else if(lhs.type().id() != ID_pointer &&
      has_char_pointer_subtype(lhs.type()))
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
            solver.make_union(lhs_data, rhs_data);
          }
        }
      }
      else
      {
        stream << log_message << "non struct with char pointer subexpr "
               << from_expr(ns, "", rhs) << "\n  * of type "
               << from_type(ns, "", rhs.type()) << eom;
      }
    }
  }
  return solver;
}

/// Maps equation to expressions contained in them and conversely expressions to
/// equations that contain them. This can be used on a subset of expressions
/// which interests us, in particular strings. Equations are identified by an
/// index of type `std::size_t` for more efficient insertion and lookup.
class equation_symbol_mappingt
{
public:
  // Record index of the equations that contain a given expression
  std::map<exprt, std::vector<std::size_t>> equations_containing;
  // Record expressions that are contained in the equation with the given index
  std::unordered_map<std::size_t, std::vector<exprt>> strings_in_equation;

  void add(const std::size_t i, const exprt &expr)
  {
    equations_containing[expr].push_back(i);
    strings_in_equation[i].push_back(expr);
  }

  std::vector<exprt> find_expressions(const std::size_t i)
  {
    return strings_in_equation[i];
  }

  std::vector<std::size_t> find_equations(const exprt &expr)
  {
    return equations_containing[expr];
  }
};

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
  else if(has_string_subtype(eq.lhs().type()))
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
      for(const auto expr : rhs_strings)
        equation_map.add(i, expr);
    }
    else if(eq.lhs().type().id() != ID_pointer &&
       has_string_subtype(eq.lhs().type()))
    {
      std::vector<exprt> lhs_strings = extract_strings_from_lhs(eq.lhs());

      for(const auto expr : lhs_strings)
        equation_map.add(i, expr);

      if(lhs_strings.empty())
      {
        stream << log_message << "non struct with string subtype "
               << from_expr(ns, "", eq.lhs()) << "\n  * of type "
               << from_type(ns, "", eq.lhs().type()) << eom;
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

void output_equations(
  std::ostream &output,
  const std::vector<equal_exprt> &equations,
  const namespacet &ns)
{
  for(std::size_t i = 0; i < equations.size(); ++i)
    output << "  [" << i << "] " << from_expr(ns, "", equations[i].lhs())
           << " == " << from_expr(ns, "", equations[i].rhs()) << std::endl;
}

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
  output_equations(debug(), equations, ns);
#endif

  debug() << "dec_solve: Build symbol solver from equations" << eom;
  // This is used by get, that's why we use a class member here
  symbol_resolve =
    generate_symbol_resolution_from_equations(equations, ns, debug());
#ifdef DEBUG
  debug() << "symbol resolve:" << eom;
  for(const auto &pair : symbol_resolve.to_vector())
    debug() << from_expr(ns, "", pair.first) << " --> "
            << from_expr(ns, "", pair.second) << eom;
#endif

  const union_find_replacet string_id_symbol_resolve =
    string_identifiers_resolution_from_equations(equations, ns, debug());
#ifdef DEBUG
  debug() << "symbol resolve string:" << eom;
  for(const auto &pair : string_id_symbol_resolve.to_vector())
  {
    debug() << from_expr(ns, "", pair.first) << " --> "
            << from_expr(ns, "", pair.second) << eom;
  }
#endif

  debug() << "dec_solve: Replacing char pointer symbols" << eom;
  replace_symbols_in_equations(symbol_resolve, equations);

  debug() << "dec_solve: Replacing string ids in function applications" << eom;
  for(equal_exprt &eq : equations)
  {
    if(can_cast_expr<function_application_exprt>(eq.rhs()))
      string_id_symbol_resolve.replace_expr(eq.rhs());
  }

#ifdef DEBUG
  output_equations(debug(), equations, ns);
#endif

  debug() << "dec_solve: Replace function applications" << eom;
  // Generator is also used by get, that's why we use a class member
  substitute_function_applications_in_equations(equations, generator);
#ifdef DEBUG
  output_equations(debug(), equations, ns);
#endif

#ifdef DEBUG
  debug() << "dec_solve: arrays_of_pointers:" << eom;
  for(auto pair : generator.get_arrays_of_pointers())
  {
    debug() << "  * " << from_expr(ns, "", pair.first) << "\t--> "
            << from_expr(ns, "", pair.second) << " : "
            << from_type(ns, "", pair.second.type()) << eom;
  }
#endif

  for(const auto &eq : equations)
  {
#ifdef DEBUG
    debug() << "dec_solve: set_to " << from_expr(ns, "", eq) << eom;
#endif
    supert::set_to(eq, true);
  }

  const auto constraints = generator.get_constraints();
  std::transform(
    constraints.begin(),
    constraints.end(),
    std::back_inserter(axioms.universal),
    [&](string_constraintt constraint) { // NOLINT
      symbol_resolve.replace_expr(constraint);
      DATA_INVARIANT(
        is_valid_string_constraint(error(), ns, constraint),
        string_refinement_invariantt(
          "string constraints satisfy their invariant"));
      return constraint;
    });

  const auto not_contains_constraints =
    generator.get_not_contains_constraints();
  std::transform(
    not_contains_constraints.begin(),
    not_contains_constraints.end(),
    std::back_inserter(axioms.not_contains),
    [&](string_not_contains_constraintt axiom) { // NOLINT
      symbol_resolve.replace_expr(axiom);
      return axiom;
    });

  for(const auto &nc_axiom : axioms.not_contains)
  {
    const auto &witness_type = [&] { // NOLINT
      const auto &rtype = to_array_type(nc_axiom.s0().type());
      const typet &index_type = rtype.size().type();
      return array_typet(index_type, infinity_exprt(index_type));
    }();
    generator.witness[nc_axiom] =
      generator.fresh_symbol("not_contains_witness", witness_type);
  }

  for(exprt lemma : generator.get_lemmas())
  {
    symbol_resolve.replace_expr(lemma);
    add_lemma(lemma);
  }

  // Initial try without index set
  const auto get = [this](const exprt &expr) { return this->get(expr); };
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
        return resultt::D_SATISFIABLE;
      }

      debug() <<  "refining..." << eom;
      // Since the model is not correct although we got SAT, we need to refine
      // the property we are checking by adding more indices to the index set,
      // and instantiating universal formulas with this indices.
      // We will then relaunch the solver with these added lemmas.
      index_sets.current.clear();
      update_index_set(index_sets, ns, current_constraints);

      display_index_set(debug(), ns, index_sets);

      if(index_sets.current.empty())
      {
        if(axioms.not_contains.empty())
        {
          error() << "dec_solve: current index set is empty, "
                  << "this should not happen" << eom;
          return resultt::D_ERROR;
        }
        else
          debug() << "dec_solve: current index set is empty" << eom;
      }
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

  debug() << "adding lemma " << from_expr(ns, "", simple_lemma) << eom;

  prop.l_set_to_true(convert(simple_lemma));
}

/// Get a model of an array and put it in a certain form.
/// If the model is incomplete or if it is too big, return no value.
/// \par parameters: an expression representing an array and an expression
/// representing an integer
/// \return an optional array expression or array_of_exprt
static optionalt<exprt> get_array(
  const std::function<exprt(const exprt &)> &super_get,
  const namespacet &ns,
  const std::size_t max_string_length,
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
    stream << "(sr::get_array) string of unknown size: "
           << from_expr(ns, "", size_val) << eom;
    return {};
  }

  auto n_opt = numeric_cast<std::size_t>(size_val);
  if(!n_opt)
  {
    stream << "(sr::get_array) size is not valid" << eom;
    return {};
  }
  std::size_t n = *n_opt;

  const array_typet ret_type(char_type, from_integer(n, index_type));
  array_exprt ret(ret_type);

  if(n>max_string_length)
  {
    stream << "(sr::get_array) long string (size=" << n << ")" << eom;
    return {};
  }

  if(n==0)
    return empty_ret;

  if(arr_val.id()=="array-list")
  {
    DATA_INVARIANT(
      arr_val.operands().size()%2==0,
      string_refinement_invariantt("and index expression must be on a symbol, "
                                   "with, array_of, if, or array, and all "
                                   "cases besides array are handled above"));
    std::map<std::size_t, exprt> initial_map;
    for(size_t i = 0; i < arr_val.operands().size(); i += 2)
    {
      exprt index = arr_val.operands()[i];
      if(auto idx = numeric_cast<std::size_t>(index))
      {
        if(*idx < n)
          initial_map[*idx] = arr_val.operands()[i + 1];
      }
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
  else
    return {};
}

/// convert the content of a string to a more readable representation. This
/// should only be used for debugging.
/// \par parameters: a constant array expression and a integer expression
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
/// \param max_string_length: limit up to which we concretize strings
/// \param stream: output stream
/// \param arr: array expression
/// \return expression corresponding to `arr` in the model
static exprt get_char_array_and_concretize(
  const std::function<exprt(const exprt &)> &super_get,
  const namespacet &ns,
  const std::size_t max_string_length,
  messaget::mstreamt &stream,
  const array_string_exprt &arr)
{
  const auto &eom = messaget::eom;
  static const std::string indent("  ");
  stream << "- " << from_expr(ns, "", arr) << ":\n";
  stream << indent << indent << "- type: " << from_type(ns, "", arr.type())
         << eom;
  const auto arr_model_opt =
    get_array(super_get, ns, max_string_length, stream, arr);
  if(arr_model_opt)
  {
    stream << indent << indent
           << "- char_array: " << from_expr(ns, "", *arr_model_opt) << eom;
    const exprt simple = simplify_expr(*arr_model_opt, ns);
    stream << indent << indent
           << "- simplified_char_array: " << from_expr(ns, "", simple) << eom;
    const exprt concretized_array =
      concretize_arrays_in_expression(simple, max_string_length, ns);
    stream << indent << indent << "- concretized_char_array: "
           << from_expr(ns, "", concretized_array) << eom;

    if(concretized_array.id() == ID_array)
    {
      stream << indent << indent << "- as_string: \""
             << string_of_array(to_array_expr(concretized_array)) << "\"\n";
    }
    else
    {
      stream << indent << "- warning: not an array" << eom;
    }

    stream << indent << indent
           << "- type: " << from_type(ns, "", concretized_array.type()) << eom;
    return concretized_array;
  }
  else
  {
    stream << indent << indent << "- incomplete model" << eom;
    return arr;
  }
}

/// Display part of the current model by mapping the variables created by the
/// solver to constant expressions given by the current model
void debug_model(
  const string_constraint_generatort &generator,
  messaget::mstreamt &stream,
  const namespacet &ns,
  const std::size_t max_string_length,
  const std::function<exprt(const exprt &)> &super_get,
  const std::vector<symbol_exprt> &boolean_symbols,
  const std::vector<symbol_exprt> &index_symbols)
{
  static const std::string indent("  ");

  stream << "debug_model:" << '\n';
  for(const auto &pointer_array : generator.get_arrays_of_pointers())
  {
    const auto arr = pointer_array.second;
    const exprt model = get_char_array_and_concretize(
      super_get, ns, max_string_length, stream, arr);

    stream << "- " << from_expr(ns, "", arr) << ":\n"
           << indent << "- pointer: " << from_expr(ns, "", pointer_array.first)
           << "\n"
           << indent << "- model: " << from_expr(ns, "", model)
           << messaget::eom;
  }

  for(const auto &symbol : boolean_symbols)
  {
    stream << " - " << symbol.get_identifier() << ": "
           << from_expr(ns, "", super_get(symbol)) << '\n';
  }

  for(const auto &symbol : index_symbols)
  {
    stream << " - " << symbol.get_identifier() << ": "
           << from_expr(ns, "", super_get(symbol)) << '\n';
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
  const array_typet &array_type = to_array_type(expr.type());

  // Map of the parts of the array that are initialized
  std::map<std::size_t, exprt> initial_map;

  // Set the last index to be sure the array will have the right length
  const auto &array_size_opt = numeric_cast<std::size_t>(array_type.size());
  if(array_size_opt && *array_size_opt > 0)
    initial_map.emplace(
      *array_size_opt - 1,
      from_integer(CHARACTER_FOR_UNKNOWN, array_type.subtype()));

  for(exprt it=expr; it.id()==ID_with; it=to_with_expr(it).old())
  {
    // Add to `initial_map` all the pairs (index,value) contained in `WITH`
    // statements
    const with_exprt &with_expr = to_with_expr(it);
    const exprt &then_expr=with_expr.new_value();
    const auto index =
      numeric_cast_v<std::size_t>(to_constant_expr(with_expr.where()));
    if(
      index < string_max_length && (!array_size_opt || index < *array_size_opt))
      initial_map.emplace(index, then_expr);
  }

  array_exprt result(array_type);
  result.operands() = fill_in_map_as_vector(initial_map);
  return result;
}

/// Fill an array represented by an array_expr by propagating values to
/// the left for unknown values. For instance `{ 24 , * , * , 42, * }` will give
/// `{ 24, 42, 42, 42, '?' }`
/// \param expr: an array expression
/// \param string_max_length: bound on the length of strings
/// \return an array expression with filled in values
exprt fill_in_array_expr(const array_exprt &expr, std::size_t string_max_length)
{
  PRECONDITION(expr.type().id() == ID_array);
  const array_typet &array_type = to_array_type(expr.type());
  PRECONDITION(array_type.subtype().id() == ID_unsignedbv);

  // Map of the parts of the array that are initialized
  std::map<std::size_t, exprt> initial_map;
  const auto &array_size_opt = numeric_cast<std::size_t>(array_type.size());

  if(array_size_opt && *array_size_opt > 0)
    initial_map.emplace(
      *array_size_opt - 1,
      from_integer(CHARACTER_FOR_UNKNOWN, array_type.subtype()));

  for(std::size_t i = 0; i < expr.operands().size(); ++i)
  {
    if(i < string_max_length && expr.operands()[i].id() != ID_unknown)
      initial_map[i] = expr.operands()[i];
  }

  array_exprt result(array_type);
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
///  * for an access in an empty array `{ }[x]` returns a fresh symbol, this
///    corresponds to a non-deterministic result
/// \param expr: an expression containing array accesses
/// \param symbol_generator: function which given a prefix and a type generates
///        a fresh symbol of the given type
/// \return an expression containing no array access
static void substitute_array_access(
  exprt &expr,
  const std::function<symbol_exprt(const irep_idt &, const typet &)>
    &symbol_generator)
{
  for(auto &op : expr.operands())
    substitute_array_access(op, symbol_generator);

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
      substitute_array_access(true_case, symbol_generator);
      exprt false_case=index_exprt(if_expr.false_case(), index_expr.index());
      substitute_array_access(false_case, symbol_generator);
      expr=if_exprt(if_expr.cond(), true_case, false_case);
      return;
    }

    DATA_INVARIANT(
      index_expr.array().id()==ID_array,
      string_refinement_invariantt("and index expression must be on a symbol, "
        "with, array_of, if, or array, and all cases besides array are handled "
        "above"));
    array_exprt &array_expr=to_array_expr(index_expr.array());

    const typet &char_type = index_expr.array().type().subtype();

    // Access to an empty array is undefined (non deterministic result)
    if(array_expr.operands().empty())
    {
      expr = symbol_generator("out_of_bound_access", char_type);
      return;
    }

    size_t last_index=array_expr.operands().size()-1;

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
    const auto lb_int = numeric_cast<mp_integer>(lbu);
    const auto ub_int = numeric_cast<mp_integer>(ubu);
    if(!lb_int || !ub_int || *ub_int<=*lb_int)
      return false_exprt();
  }

  const auto lbe = numeric_cast_v<mp_integer>(axiom.exists_lower_bound());
  const auto ube = numeric_cast_v<mp_integer>(axiom.exists_upper_bound());

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
    const auto lb_int = numeric_cast<mp_integer>(lb);
    const auto ub_int = numeric_cast<mp_integer>(ub);
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
/// \param ns: namespace, used to determine what is an array of character
/// \return the interpreted expression
exprt concretize_arrays_in_expression(
  exprt expr,
  std::size_t string_max_length,
  const namespacet &ns)
{
  auto it=expr.depth_begin();
  const auto end=expr.depth_end();
  while(it!=end)
  {
    if(is_char_array_type(it->type(), ns))
    {
      if(it->id() == ID_with || it->id() == ID_array_of)
      {
        it.mutate() = fill_in_array_with_expr(*it, string_max_length);
        it.next_sibling_or_parent();
      }
      else if(it->id() == ID_array)
      {
        it.mutate() = fill_in_array_expr(to_array_expr(*it), string_max_length);
        it.next_sibling_or_parent();
      }
      else
        ++it; // ignoring other expressions
    }
    else
      ++it;
  }
  return expr;
}

/// Debugging function which outputs the different steps an axiom goes through
/// to be checked in check axioms.
static void debug_check_axioms_step(
  messaget::mstreamt &stream,
  const namespacet &ns,
  const exprt &axiom,
  const exprt &axiom_in_model,
  const exprt &negaxiom,
  const exprt &with_concretized_arrays)
{
  static const std::string indent = "  ";
  static const std::string indent2 = "    ";
  stream << indent2 << "- axiom:\n" << indent2 << indent;

  if(axiom.id() == ID_string_constraint)
    stream << from_expr(ns, "", to_string_constraint(axiom));
  else if(axiom.id() == ID_string_not_contains_constraint)
    stream << from_expr(ns, "", to_string_not_contains_constraint(axiom));
  else
    stream << from_expr(ns, "", axiom);
  stream << '\n' << indent2 << "- axiom_in_model:\n" << indent2 << indent;

  if(axiom_in_model.id() == ID_string_constraint)
    stream << from_expr(ns, "", to_string_constraint(axiom_in_model));
  else if(axiom_in_model.id() == ID_string_not_contains_constraint)
    stream << from_expr(
      ns, "", to_string_not_contains_constraint(axiom_in_model));
  else
    stream << from_expr(ns, "", axiom_in_model);

  stream << '\n'
         << indent2 << "- negated_axiom:\n"
         << indent2 << indent << from_expr(ns, "", negaxiom) << '\n';
  stream << indent2 << "- negated_axiom_with_concretized_arrays:\n"
         << indent2 << indent << from_expr(ns, "", with_concretized_arrays)
         << '\n';
}

/// \return true if the current model satisfies all the axioms
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
  const union_find_replacet &symbol_resolve)
{
  const auto eom=messaget::eom;
  static const std::string indent = "  ";
  static const std::string indent2 = "    ";
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
    stream << "  - " << from_expr(ns, "", pair.first) << " --> "
           << from_expr(ns, "", pair.second) << eom;

#ifdef DEBUG
  debug_model(
    generator,
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
    negaxiom = simplify_expr(negaxiom, ns);
    exprt with_concretized_arrays =
      concretize_arrays_in_expression(negaxiom, max_string_length, ns);

    substitute_array_access(with_concretized_arrays, gen_symbol);

    stream << indent << i << ".\n";
    debug_check_axioms_step(
      stream, ns, axiom, axiom_in_model, negaxiom, with_concretized_arrays);

    if(const auto &witness=
       find_counter_example(ns, ui, with_concretized_arrays, univ_var))
    {
      stream << indent2 << "- violated_for: " << univ_var.get_identifier()
             << "=" << from_expr(ns, "", *witness) << eom;
      violated[i]=*witness;
    }
    else
      stream << indent2 << "- correct" << eom;
  }

  // Maps from indexes of violated not_contains axiom to a witness of violation
  std::map<std::size_t, exprt> violated_not_contains;

  stream << "there are " << axioms.not_contains.size()
         << " not_contains axioms" << eom;
  for(std::size_t i = 0; i < axioms.not_contains.size(); i++)
  {
    const string_not_contains_constraintt &nc_axiom=axioms.not_contains[i];
    const exprt &univ_bound_inf=nc_axiom.univ_lower_bound();
    const exprt &univ_bound_sup=nc_axiom.univ_upper_bound();
    const exprt &prem=nc_axiom.premise();
    const exprt &exists_bound_inf=nc_axiom.exists_lower_bound();
    const exprt &exists_bound_sup=nc_axiom.exists_upper_bound();
    const array_string_exprt &s0 = nc_axiom.s0();
    const array_string_exprt &s1 = nc_axiom.s1();

    symbol_exprt univ_var=generator.fresh_univ_index(
      "not_contains_univ_var", nc_axiom.s0().length().type());
    string_not_contains_constraintt nc_axiom_in_model(
      get(univ_bound_inf),
      get(univ_bound_sup),
      get(prem),
      get(exists_bound_inf),
      get(exists_bound_sup),
      to_array_string_expr(get(s0)),
      to_array_string_expr(get(s1)));

    // necessary so that expressions such as `1 + (3 - (TRUE ? 0 : 0))` do not
    // appear in bounds
    nc_axiom_in_model =
      to_string_not_contains_constraint(simplify_expr(nc_axiom_in_model, ns));

    exprt negaxiom =
      negation_of_not_contains_constraint(nc_axiom_in_model, univ_var);

    negaxiom = simplify_expr(negaxiom, ns);
    exprt with_concrete_arrays =
      concretize_arrays_in_expression(negaxiom, max_string_length, ns);

    substitute_array_access(with_concrete_arrays, gen_symbol);

    stream << indent << i << ".\n";
    debug_check_axioms_step(
      stream, ns, nc_axiom, nc_axiom_in_model, negaxiom, with_concrete_arrays);

    if(const auto witness = find_counter_example(ns, ui, negaxiom, univ_var))
    {
      stream << indent2 << "- violated_for: " << univ_var.get_identifier()
             << "=" << from_expr(ns, "", *witness) << eom;
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

        stream << "    -  " << from_expr(ns, "", counter) << eom;
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
      it->second == 0,
      string_refinement_invariantt(
        "a proper function must have exactly one "
        "occurrences after reduction, or it cancelled out, and it does not"
        " have one"));
    stream << "in string_refinementt::compute_inverse_function:"
           << " warning: occurrences of qvar cancelled out " << messaget::eom;
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
    const exprt cur = to_process.back();
    to_process.pop_back();
    if(cur.id() == ID_index && is_char_type(cur.type()))
    {
      const index_exprt &index_expr = to_index_expr(cur);
      const exprt &s = index_expr.array();
      const exprt &i = index_expr.index();

      if(s.id() == ID_array)
      {
        for(std::size_t j = 0; j < s.operands().size(); ++j)
          add_to_index_set(index_set, ns, s, from_integer(j, i.type()));
      }
      else
      {
        const bool has_quant_var = find_qvar(i, qvar);

        // if cur is of the form s[i] and no quantified variable appears in i
        if(!has_quant_var)
        {
          add_to_index_set(index_set, ns, s, i);
        }
        else
        {
          // otherwise we add k-1
          exprt copy(i);
          const minus_exprt kminus1(
            axiom.upper_bound(), from_integer(1, axiom.upper_bound().type()));
          replace_expr(qvar, kminus1, copy);
          add_to_index_set(index_set, ns, s, copy);
        }
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
  const auto it=std::find_if(
    expr.depth_begin(),
    expr.depth_end(),
    [&] (const exprt &e) -> bool
    {
      return e.id()==ID_index
             && to_index_expr(e).array()==str
             && find_qvar(to_index_expr(e).index(), qvar);
    });

  return it==expr.depth_end()
         ?nil_exprt()
         :to_index_expr(*it).index();
}

/// Instantiates a string constraint by substituting the quantifiers.
/// For a string constraint of the form \f$\forall q. P(x)\f$,
/// substitute `qvar` the universally quantified variable of `axiom`, by
/// an index `val`, in `axiom`, so that the index used for `str` equals `val`.
/// For instance, if `axiom` corresponds to \f$\forall q. s[q+x]={\tt 'a'} \land
/// t[q]={\tt 'b'} \f$, `instantiate(axiom,s,v)` would return an expression for
/// \f$s[v]={\tt 'a'} \land t[v-x]={\tt 'b'}\f$.
/// \param stream: a message stream
/// \param axiom: a universally quantified formula `axiom`
/// \param str: an array of characters
/// \param val: an index expression
/// \return instantiated formula
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
  const string_constraint_generatort &generator)
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
    operand = substitute_array_lists(operand, string_max_length);

  if(expr.id()=="array-list")
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
/// The difference with supert::get is that arrays of characters need to be
/// concretized. See concretize_arrays_in_expression for how it is done.
/// \param expr: an expression
/// \return evaluated expression
exprt string_refinementt::get(const exprt &expr) const
{
  // clang-format off
  const auto super_get = [this](const exprt &expr)
  {
    return supert::get(expr);
  };
  // clang-format on

  exprt ecopy(expr);
  (void)symbol_resolve.replace_expr(ecopy);

  if(is_char_array_type(ecopy.type(), ns))
  {
    array_string_exprt &arr = to_array_string_expr(ecopy);
    arr.length() = generator.get_length_of_string_array(arr);
    const auto arr_model_opt =
      get_array(super_get, ns, generator.max_string_length, debug(), arr);
    // \todo Refactor with get array in model
    if(arr_model_opt)
    {
      const exprt arr_model = simplify_expr(*arr_model_opt, ns);
      const exprt concretized_array = concretize_arrays_in_expression(
        arr_model, generator.max_string_length, ns);
      return concretized_array;
    }
    else
    {
      auto set = generator.get_created_strings();
      if(set.find(arr) != set.end())
      {
        exprt length = super_get(arr.length());
        if(const auto n = numeric_cast<std::size_t>(length))
        {
          exprt arr_model =
            array_exprt(array_typet(arr.type().subtype(), length));
          for(size_t i = 0; i < *n; i++)
            arr_model.copy_to_operands(exprt(ID_unknown, arr.type().subtype()));
          const exprt concretized_array = concretize_arrays_in_expression(
            arr_model, generator.max_string_length, ns);
          return concretized_array;
        }
      }
      return arr;
    }
  }
  return supert::get(ecopy);
}

/// Creates a solver with `axiom` as the only formula added and runs it. If it
/// is SAT, then true is returned and the given evaluation of `var` is stored
/// in `witness`. If UNSAT, then what witness is is undefined.
/// \param ns: namespace
/// \param ui: message handler
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
static bool universal_only_in_index(const string_constraintt &expr)
{
  for(auto it = expr.body().depth_begin(); it != expr.body().depth_end();)
  {
    if(*it == expr.univ_var())
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

    // Condition 3: f must be linear in the quantified variable
    if(!is_linear_arithmetic_expr(rep, expr.univ_var()))
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

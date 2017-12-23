// Author: DiffBlue Ltd.

#include <stack>
#include "string_constraint.h"
#include <util/simplify_expr.h>
#include <util/expr_iterator.h>

void replace(string_constraintt &axiom, const replace_mapt &symbol_resolve)
{
  replace_expr(symbol_resolve, axiom.index_guard);
  replace_expr(symbol_resolve, axiom.body);
  replace_expr(symbol_resolve, axiom.univ_var);
  replace_expr(symbol_resolve, axiom.upper_bound);
  replace_expr(symbol_resolve, axiom.lower_bound);
}

exprt univ_within_bounds(const string_constraintt &axiom)
{
  return and_exprt(
    binary_relation_exprt(axiom.lower_bound, ID_le, axiom.univ_var),
    binary_relation_exprt(axiom.upper_bound, ID_gt, axiom.univ_var));
}

std::string to_string(const string_constraintt &expr)
{
  std::ostringstream out;
  out << "forall " << format(expr.univ_var) << " in ["
      << format(expr.lower_bound) << ", " << format(expr.upper_bound) << "). "
      << format(expr.index_guard) << " => " << format(expr.body);
  return out.str();
}

std::string to_string(const string_not_contains_constraintt &expr)
{
  std::ostringstream out;
  out << "forall x in [" << format(expr.univ_lower_bound()) << ", "
      << format(expr.univ_upper_bound()) << "). " << format(expr.premise())
      << " => ("
      << "exists y in [" << format(expr.exists_lower_bound()) << ", "
      << format(expr.exists_upper_bound()) << "). " << format(expr.s0())
      << "[x+y] != " << format(expr.s1()) << "[y])";
  return out.str();
}

const string_not_contains_constraintt &
to_string_not_contains_constraint(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_string_not_contains_constraint);
  DATA_INVARIANT(
    expr.operands().size() == 7,
    string_refinement_invariantt(
      "string_not_contains_constraintt must have 7 "
      "operands"));
  return static_cast<const string_not_contains_constraintt &>(expr);
}

string_not_contains_constraintt &to_string_not_contains_constraint(exprt &expr)
{
  PRECONDITION(expr.id() == ID_string_not_contains_constraint);
  DATA_INVARIANT(
    expr.operands().size() == 7,
    string_refinement_invariantt(
      "string_not_contains_constraintt must have 7 "
      "operands"));
  return static_cast<string_not_contains_constraintt &>(expr);
}

typedef std::map<exprt, std::vector<exprt>> array_index_mapt;

static array_index_mapt gather_indices(const exprt &expr)
{
  array_index_mapt indices;
  std::for_each(
    expr.depth_begin(),
    expr.depth_end(),
    [&](const exprt &expr) { // NOLINT
      if(const auto index_expr = expr_try_dynamic_cast<const index_exprt>(expr))
        indices[index_expr->array()].push_back(index_expr->index());
    });
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
      const auto find_qvar = std::find(it->depth_begin(), it->depth_end(), var);
      if(find_qvar != it->depth_end())
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
/// \param [in] expr: The string constraint to check
/// \return true if the universal variable only occurs in index expressions,
///   false otherwise.
static bool universal_only_in_index(const string_constraintt &expr)
{
  for(auto it = expr.body.depth_begin(); it != expr.body.depth_end();)
  {
    if(*it == expr.univ_var)
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
bool is_valid_string_constraint(
  messaget::mstreamt &stream,
  const namespacet &ns,
  const string_constraintt &constraint)
{
  const auto eom = messaget::eom;
  // Condition 1: The index guard cannot contain any string indices
  const array_index_mapt premise_indices =
    gather_indices(constraint.index_guard);
  if(!premise_indices.empty())
  {
    stream << "Index guard has indices: " << to_string(constraint)
           << ", map: {";
    for(const auto &pair : premise_indices)
    {
      stream << format(pair.first) << ": {";
      for(const auto &i : pair.second)
        stream << format(i) << ", ";
    }
    stream << "}}" << eom;
    return false;
  }

  const array_index_mapt body_indices = gather_indices(constraint.body);
  // Must validate for each string. Note that we have an invariant that the
  // second value in the pair is non-empty.
  for(const auto &pair : body_indices)
  {
    // Condition 2: All indices of the same string must be the of the same form
    const exprt rep = pair.second.back();
    for(size_t j = 0; j < pair.second.size() - 1; j++)
    {
      const exprt i = pair.second[j];
      const equal_exprt equals(rep, i);
      const exprt result = simplify_expr(equals, ns);
      if(result.is_false())
      {
        stream << "Indices not equal: " << to_string(constraint)
               << ", str: " << format(pair.first) << eom;
        return false;
      }
    }

    // Condition 3: f must be linear
    if(!is_linear_arithmetic_expr(rep, constraint.univ_var))
    {
      stream << "f is not linear: " << to_string(constraint)
             << ", str: " << format(pair.first) << eom;
      return false;
    }

    // Condition 4: the quantified variable can only occur in indices in the
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

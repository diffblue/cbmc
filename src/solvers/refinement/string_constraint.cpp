#include <stack>
#include "string_constraint.h"
#include <util/simplify_expr.h>

void replace(string_constraintt &axiom, const replace_mapt& symbol_resolve)
{
  replace_expr(symbol_resolve, axiom.premise);
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

std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const string_constraintt &expr)
{
  return "forall "+from_expr(ns, identifier, expr.univ_var)+" in ["+
    from_expr(ns, identifier, expr.lower_bound)+", "+
    from_expr(ns, identifier, expr.upper_bound)+"). "+
    from_expr(ns, identifier, expr.premise)+" => "+
    from_expr(ns, identifier, expr.body);
}

std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const string_not_contains_constraintt &expr)
{
  return "forall x in ["+
    from_expr(ns, identifier, expr.univ_lower_bound())+", "+
    from_expr(ns, identifier, expr.univ_upper_bound())+"). "+
    from_expr(ns, identifier, expr.premise())+" => ("+
    "exists y in ["+from_expr(ns, identifier, expr.exists_lower_bound())+", "+
    from_expr(ns, identifier, expr.exists_upper_bound())+"). "+
    from_expr(ns, identifier, expr.s0())+"[x+y] != "+
    from_expr(ns, identifier, expr.s1())+"[y])";
}

const string_not_contains_constraintt
&to_string_not_contains_constraint(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_string_not_contains_constraint);
  DATA_INVARIANT(
    expr.operands().size()==7,
    string_refinement_invariantt("string_not_contains_constraintt must have 7 "
      "operands"));
  return static_cast<const string_not_contains_constraintt &>(expr);
}

string_not_contains_constraintt
&to_string_not_contains_constraint(exprt &expr)
{
  PRECONDITION(expr.id()==ID_string_not_contains_constraint);
  DATA_INVARIANT(
    expr.operands().size()==7,
    string_refinement_invariantt("string_not_contains_constraintt must have 7 "
      "operands"));
  return static_cast<string_not_contains_constraintt &>(expr);
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
  stack.push(valuet(expr.body, 0));
  while(!stack.empty())
  {
    // Inspect current value
    const valuet cur=stack.top();
    stack.pop();
    const exprt e=cur.first;
    const unsigned index_depth=cur.second;
    const unsigned child_index_depth=index_depth+(e.id()==ID_index?0:1);

    // If we found the universal variable not in an index_exprt, fail
    if(e==expr.univ_var && index_depth==0)
      return false;
    else
      forall_operands(it, e)
        stack.push(valuet(*it, child_index_depth));
  }
  return true;
}

bool is_valid_string_constraint(
  messaget::mstreamt &stream,
  const namespacet &ns,
  const string_constraintt &expr)
{
  const auto eom=messaget::eom;
  // Condition 1: The premise cannot contain any string indices
  const array_index_mapt premise_indices=gather_indices(expr.premise);
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

  const array_index_mapt body_indices=gather_indices(expr.body);
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

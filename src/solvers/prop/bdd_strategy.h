/*******************************************************************\

Module: BDDs

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// General definition of strategies for converting BDDs

#ifndef CPROVER_SOLVERS_PROP_BDD_STRATEGY_H
#define CPROVER_SOLVERS_PROP_BDD_STRATEGY_H

/// Template for applying a transformation to a BDD.
/// The user provides implementation for \c leaf, \c make_or, \c make_and,
/// \c make_not, and \c make_if_then_else and the template provides
/// implementation of \c apply which goes through the BDD and applies the
/// relevant function depending on the type of node.
template <typename returnt, typename internal_statet>
class bdd_strategyt
{
public:
  explicit bdd_strategyt(internal_statet internal_state)
    : internal_state(std::move(internal_state))
  {
  }

  returnt apply(const bdd_nodet &bdd_node)
  {
    std::unordered_map<bdd_nodet::idt, returnt> cache;
    return apply(bdd_node, cache);
  }

private:
  internal_statet internal_state;
  returnt leaf(const bdd_nodet::indext &);
  returnt make_false();
  returnt make_true();
  returnt make_or(const returnt &, const returnt &);
  returnt make_and(const returnt &, const returnt &);
  returnt make_not(const returnt &);
  returnt make_if_then_else(const returnt &, const returnt &, const returnt &);

  returnt
  apply(const bdd_nodet &r, std::unordered_map<bdd_nodet::idt, returnt> &cache);
};

template <typename returnt, typename internal_statet>
returnt bdd_strategyt<returnt, internal_statet>::apply(
  const bdd_nodet &r,
  std::unordered_map<bdd_nodet::idt, returnt> &cache)
{
  if(r.is_constant())
  {
    if(r.is_complement())
      return make_false();
    else
      return make_true();
  }
  auto index = narrow<std::size_t>(r.index());
  returnt node_result = leaf(index);

  // Look-up cache for already computed value
  // (`false` used as temporary value)
  auto insert_result = cache.emplace(r.id(), make_false());
  if(insert_result.second)
  {
    returnt result_ignoring_complement = [&]() -> returnt {
      if(r.else_branch().is_constant())
      {
        if(r.then_branch().is_constant())
        {
          if(r.else_branch().is_complement())
            return node_result;
          return make_not(node_result);
        }
        else
        {
          if(r.else_branch().is_complement())
            return make_and(node_result, apply(r.then_branch(), cache));
          return make_or(make_not(node_result), apply(r.then_branch(), cache));
        }
      }
      else if(r.then_branch().is_constant())
      {
        if(r.then_branch().is_complement())
          return make_and(make_not(node_result), apply(r.else_branch(), cache));
        return make_or(node_result, apply(r.else_branch(), cache));
      }
      return make_if_then_else(
        node_result,
        apply(r.then_branch(), cache),
        apply(r.else_branch(), cache));
    }();
    insert_result.first->second =
      r.is_complement() ? make_not(std::move(result_ignoring_complement))
                        : std::move(result_ignoring_complement);
  }
  return insert_result.first->second;
}

#endif // CPROVER_SOLVERS_PROP_BDD_STRATEGY_H

template<class populationt>
bool family_selectiont<populationt>::can_mutate() const
{
  return !parents.empty() && !children.empty();
}

#define CEGIS_FAMILY_SELECTION_MIN_NUM_OPS 2u

template<class populationt>
bool family_selectiont<populationt>::can_cross() const
{
  return parents.size() >= CEGIS_FAMILY_SELECTION_MIN_NUM_OPS
      && children.size() >= CEGIS_FAMILY_SELECTION_MIN_NUM_OPS;
}

template<class populationt>
typename populationt::value_type &family_selectiont<populationt>::mutation_lhs()
{
  return *children.front();
}

template<class populationt>
const typename populationt::value_type &family_selectiont<populationt>::mutation_rhs() const
{
  return *parents.front();
}

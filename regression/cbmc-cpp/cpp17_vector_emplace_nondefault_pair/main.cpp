// vector<pair<T, U>>::emplace_back(t, u) where T has a user
// constructor and NO default constructor: instantiating emplace_back
// fails "found no match for symbol 'emplace_back'".  pair's
// constructor set is constrained via SFINAE on
// is_constructible/is_default_constructible ([pairs.pair]); with a
// non-default-constructible T some constrained candidate evaluation
// fails hard instead of being discarded ([temp.deduct]/8 -- only the
// immediate context), killing the whole overload.  Works with
// pair<int, unsigned long> (both trivially constructible), with an
// aggregate T (default-constructible), and with DIRECT pair
// construction (no emplace_back forwarding).  Same defect family as
// cpp17_umap_emplace_mixed_categories (hashtable nodes hold
// pair<const _Key, _Tp>); distilled from std::pair<ssa_exprt,
// unsigned long> in util/sharing_node.h (the goto_symex_state.h /
// abstract_environment dog-food TUs).
#include <utility>
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);

struct symbolish
{
  int x;
  symbolish(int v) : x(v)
  {
  }
};

int main()
{
  std::vector<std::pair<symbolish, unsigned long>> v;
  v.emplace_back(symbolish{1}, 2ul);
  __CPROVER_assert(v.size() == 1, "emplace_back pair with non-default-constructible member");
  return 0;
}

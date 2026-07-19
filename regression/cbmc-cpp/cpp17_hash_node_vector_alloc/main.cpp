// N5008 [temp.inst], [allocator.requirements]: instantiating
// std::vector<K> requires resolving _Vector_base<K, allocator<K>>'s
// nested typedef _Tp_alloc_type (the allocator rebound to K via
// __gnu_cxx::__alloc_traits::rebind).
//
// This used to fail in three layers, all fixed: (1) member class
// templates dropped from truncated instances (per-member recovery +
// member-template registration); (2) rebind ambiguity ([temp.names]/3
// scope-restricted lookup); (3) push_back dropped through a hybrid
// half-substituted instance created by resolving a deduction variable
// by short name through the enclosing template map ([temp.deduct]/2
// clean slate; see cpp17_push_back_after_unordered_set_decl).
//
// g++/clang++ verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);
#include <unordered_set>
#include <vector>

struct K
{
  unsigned n;
  bool operator==(const K &o) const
  {
    return n == o.n;
  }
};

template <>
struct std::hash<K>
{
  std::size_t operator()(const K &k) const
  {
    return k.n;
  }
};

int main()
{
  std::unordered_set<K> s;
  s.insert(K{1});
  std::vector<K> v;
  v.reserve(2);
  v.push_back(K{7});
  __CPROVER_assert(v[0].n == 7, "vector element after hash-node rebind");
  return 0;
}

// N5008 [temp.inst], [allocator.requirements]: instantiating
// std::vector<K> requires resolving _Vector_base<K, allocator<K>>'s
// nested typedef _Tp_alloc_type (the allocator rebound to K via
// __gnu_cxx::__alloc_traits::rebind).
//
// KNOWNBUG: when std::unordered_set<K>::insert has been instantiated
// FIRST (which materializes allocator<_Hash_node<K,...>> and its
// rebind machinery for the same K), the later std::vector<K>
// instantiation fails to resolve _Tp_alloc_type and pointer ("symbol
// '_Tp_alloc_type' is unknown"), leaving the vector machinery
// incomplete: v[0] reads garbage.  Without the preceding
// unordered_set insert (or with the vector instantiated first) the
// same vector code verifies.  Order-dependent contamination of the
// rebind resolution.
//
// g++/clang++ verify at runtime.  Flip to CORE when fixed.
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

// N5008 [temp.inst]/1, [temp.deduct]/8: merely naming
// std::unordered_set<K>* must not affect the later instantiation of
// std::vector<K>::push_back.
//
// This used to fail ("no body for callee std::vector<...>::push_back")
// after a bare std::unordered_set<K> mention: while disambiguating
// std::hash against the pattern hash<vector<bool, _Alloc>>
// (stl_bvector.h), the pattern's own _Alloc -- an explicitly-unassigned
// deduction variable -- was resolved BY SHORT NAME through the
// enclosing unordered_set instantiation's _Alloc = allocator<K>
// (violating [temp.deduct]/2's clean slate), instantiating a hybrid
// vector<bool, allocator<K>> whose half-substituted cached instances
// (a truncated __gnu_cxx::__alloc_traits among them) later poisoned
// vector<K>.
//
// g++/clang++ accept and verify at runtime.
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
  std::unordered_set<K> *sp = nullptr; // mere mention poisons vector<K>
  (void)sp;
  std::vector<K> v;
  v.push_back(K{7});
  __CPROVER_assert(v[0].n == 7, "vector element usable");
  return 0;
}

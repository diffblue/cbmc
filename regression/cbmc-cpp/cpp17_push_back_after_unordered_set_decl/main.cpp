// N5008 [temp.inst]/1, [temp.deduct]/8: merely naming
// std::unordered_set<K>* must not affect the later instantiation of
// std::vector<K>::push_back.
//
// KNOWNBUG: after std::unordered_set<K> is mentioned (a pointer
// declaration suffices -- no object, no insert), the body of
// std::vector<K>::push_back is silently dropped: its _M_realloc_append
// path evaluates vector::_S_use_relocate() to FALSE in the enable_if
// of a return type ('type' unknown in std::enable_if<0,void> -- a
// silent [temp.deduct]/8-style throw), even though CBMC's stdlib model
// overrides _S_nothrow_relocate/_S_use_relocate to true.  The override
// covers the function bodies but not this constexpr use in a return
// type.  Symptom: "no body for callee std::vector<...>::push_back".
// Without the unordered_set mention the same code verifies
// (cpp11_vector_of_class_push_back-style tests pass).
//
// g++/clang++ accept and verify at runtime.  Flip to CORE when fixed.
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

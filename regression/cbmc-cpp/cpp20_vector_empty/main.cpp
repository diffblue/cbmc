// Genuine (non-vacuous) verification of an empty std::vector.
//
// Instantiating std::vector<int> elaborates its member iterator typedefs
//   typedef __gnu_cxx::__normal_iterator<pointer, vector>       iterator;
//   typedef __gnu_cxx::__normal_iterator<const_pointer, vector> const_iterator;
//   typedef std::reverse_iterator<const_iterator> const_reverse_iterator;
// The first two are *self-referential* (their type names the enclosing,
// still-incomplete `vector`) and cannot be eagerly instantiated at that point.
// They are therefore registered lazily ([temp.inst]/1-2, [dcl.typedef]: a
// member typedef declares the member and forms the alias without instantiating
// the aliased template's definition -- a typedef-name may denote an incomplete
// type), so the sibling `const_reverse_iterator` (and other uses) can still
// resolve `const_iterator`.  Before the fix, the self-referential typedefs were
// dropped, so `const_iterator` was unknown, the enclosing statement aborted,
// and the assertion below was silently dropped (vacuous SUCCESS).
#include <vector>
int main()
{
  std::vector<int> v;
  __CPROVER_assert(v.size() == 0, "empty vector has size 0");
  return 0;
}

// Genuine (non-vacuous) verification of std::find over a *populated* std::vector.
//
// std::find(v.begin(), v.end(), x) iterates with __normal_iterator, comparing
// *__first == x and advancing ++__first until __last.  This requires the
// instantiated iterator type __normal_iterator<pointer, vector> to actually
// have its member functions (operator*, operator++, operator==/!=), which are
// instantiated on demand once the iterator's inert C++20 `iterator_concept`
// alias is kept lazy instead of abandoning the iterator's class body (see
// cpp_typecheck_compound_type.cpp; [iterator.concepts.general], [temp.inst]/1-2,
// [dcl.typedef]).  Before that fix the iterator was method-less, the loop body
// could not be elaborated, and the search degenerated to nondeterminism.
//
// The result is checked exactly: the element is found (it != end) and the
// found value is the searched-for one.  The companion negative check (asserting
// the wrong value) fails, confirming this is non-vacuous.
#include <algorithm>
#include <vector>

int main()
{
  std::vector<int> v;
  v.push_back(1);
  v.push_back(2);
  v.push_back(3);
  std::vector<int>::iterator it = std::find(v.begin(), v.end(), 2);
  __CPROVER_assert(it != v.end(), "element 2 is found");
  __CPROVER_assert(*it == 2, "found element has the searched value");
  return 0;
}

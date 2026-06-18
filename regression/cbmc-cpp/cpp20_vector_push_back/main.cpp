// Genuine (non-vacuous) verification of a *populated* std::vector.
//
// push_back grows the buffer through _M_realloc_insert, which computes the
// insertion offset with __gnu_cxx::operator-(__normal_iterator,
// __normal_iterator) -> __lhs.base() - __rhs.base().  That requires the
// instantiated iterator type __normal_iterator<pointer, vector> to actually
// have its member functions (base(), operator*, operator++, ...).
//
// During std::vector<int> elaboration the iterator instance is completed while
// it (and the enclosing vector) are still incomplete: the C++20 member alias
//   using iterator_concept = std::__detail::__iter_concept<_Iterator>;
// reaches back through the incomplete iterator via the iterator-concept
// machinery and cannot be elaborated yet.  Per [temp.inst]/1-2 and
// [dcl.typedef], that member typedef declares the member and forms the aliased
// type but does not require the aliased template's *definition*; a typedef-name
// may denote an incomplete type.  The failure to elaborate that one alias must
// therefore not abandon the rest of the class body.  Before the fix it did:
// every later member -- crucially the member *functions* operator*/base/... --
// was dropped, leaving the iterator instance complete-looking but method-less.
// operator-'s body then could not find base(), its body was emptied to a
// nondeterministic stub, and `v.size()` after push_back became nondet, so the
// assertions below were either violated or vacuous.
//
// With the alias kept lazy and the sibling methods instantiated on demand, the
// populated vector verifies genuinely: size and stored element value are exact.
#include <vector>

int main()
{
  std::vector<int> v;
  v.push_back(7);
  __CPROVER_assert(v.size() == 1, "size is 1 after one push_back");
  __CPROVER_assert(v[0] == 7, "stored element value is exact");
  return 0;
}

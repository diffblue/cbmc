// N5008 [temp.inst]/4: a member function of a class template
// specialization is implicitly instantiated when odr-used.
// unordered_set's insert taking a value is provided by the
// std::__detail::_Insert CRTP mixin base; the call below odr-uses
// _Insert<...>::insert(value_type&&), which must therefore be
// instantiated.
//
// This test tracked a CHAIN of five defects, all fixed: the deferred-
// member drain's tag-strip, friendship-based private-base conversion
// ([class.access.base]/4-5), condition-declaration scoping
// ([stmt.pre]/6), models for the compiled-library
// _Prime_rehash_policy::_M_next_bkt/_M_need_rehash, and the
// destructor-via-typedef-name substitution ([expr.prim.id.dtor]/1,
// [basic.lookup.qual]/6) that _M_deallocate_node_ptr's
// `__n->~__node_type()` needs.
//
// g++/clang++ verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);
#include <unordered_set>

int main()
{
  std::unordered_set<int> s;
  s.insert(1);
  __CPROVER_assert(s.count(1) == 1, "inserted element is found");
  __CPROVER_assert(s.count(2) == 0, "absent element is not found");
  return 0;
}

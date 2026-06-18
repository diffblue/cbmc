// C++ [temp.variadic]/8 (sizeof...): `sizeof...(Pack)` is the number of elements
// in the pack.  This works in a member function body but not in a static data
// member's initializer, where the pack is collapsed to a single element (or to
// the wrong count) during class-template instantiation.
//
// KNOWNBUG: sizeof...(T) in a static data member initializer yields the wrong
// value for a multi-element pack (and for an empty pack).  Reclassify CORE once
// sizeof... is evaluated against the full instantiated pack in this context.

template <typename... T>
struct counter
{
  static const int n = sizeof...(T);
};

int main()
{
  __CPROVER_assert(
    counter<int, char, long>::n == 3, "sizeof...(T) in static init is 3");
  __CPROVER_assert(counter<>::n == 0, "sizeof...(T) in static init is 0 (empty)");
  return 0;
}

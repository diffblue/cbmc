// N5008 [temp.deduct.call]/4.3: when a function parameter is a class
// template-id `Base<...>` and the argument is of a derived class type, the
// template arguments are deduced from the base class of the argument that is a
// specialization of that template.  Here `get_head(Base<_Head, _Tail...>&)` is
// called with a `Derived<int>` argument, whose base is `Base<int>`, so
// `_Head = int` and `_Tail` is the empty pack.
//
// KNOWNBUG: when this derived-to-base deduction first instantiates the callee
// (with an empty trailing pack `_Tail`) from *within a function body* (here
// `wrapper`, type-checked on demand while converting `main`), CBMC builds a
// malformed instance whose parameter list is dropped, so the call is never
// emitted and the function returns a nondet value.  The same call works when
// the callee is first instantiated by a direct (top-level) call, and a single-
// parameter `Base<_Head>&` (no trailing pack) also works -- so the trigger is
// the empty trailing pack in the parameter type during the nested-body
// instantiation.
//
// `get_head(__d)` must return the base subobject's `v` (42).  Assertion 1 must
// SUCCEED once fixed; assertion 2 (a wrong value) must FAIL, proving
// non-vacuity.

template <typename...>
struct Base;

template <typename _Head>
struct Base<_Head>
{
  _Head v;
};

template <typename _Head, typename... _Tail>
_Head &get_head(Base<_Head, _Tail...> &__b)
{
  return __b.v;
}

template <typename... _Elements>
struct Derived : Base<_Elements...>
{
};

int wrapper(Derived<int> &__d)
{
  return get_head(__d);
}

int main()
{
  Derived<int> d;
  static_cast<Base<int> &>(d).v = 42;
  int a = wrapper(d);
  __CPROVER_assert(
    a == 42, "derived-to-base pack-parameter call in a function body");
  __CPROVER_assert(a == 999, "WRONG (must FAIL)");
  return 0;
}

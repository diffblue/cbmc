// N5008 [temp.deduct.call]/4.3: when a function parameter is a class
// template-id `Base<...>` and the argument is of a derived class type, the
// template arguments are deduced from the base class of the argument that is a
// specialization of that template.  Here `get_head(Base<_Head, _Tail...>&)` is
// called with a `Derived<int>` argument, whose base is `Base<int>`, so
// `_Head = int` and `_Tail` is the empty pack.
//
// Regression: instantiating the callee with an empty trailing pack `_Tail`
// used to drop the whole parameter `__b` (its type `Base<_Head, _Tail...>&`
// references the empty pack `_Tail` nested in a template-argument expansion),
// leaving `get_head<int>` with an empty parameter list and an unbindable call
// (so the function returned a nondet value).  Per N5008 [temp.variadic]/7 the
// empty expansion only collapses the argument list (`Base<_Head>`); the
// parameter itself must be kept.  Now fixed in cpp_instantiate_template.cpp.
//
// `get_head(__d)` must return the base subobject's `v` (42).  Assertion 1
// SUCCEEDs; assertion 2 (a wrong value) FAILs, proving non-vacuity.

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

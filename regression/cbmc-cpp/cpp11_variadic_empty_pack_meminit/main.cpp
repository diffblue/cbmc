// N5008 13.7.4 [temp.variadic]/16: "The instantiation of any other pack
// expansion produces a list of elements E1, E2, ..., EN. ... When N is zero,
// the instantiation of the expansion produces an empty list."  A
// mem-initializer-list whose mem-initializer-id denotes a base class is such a
// context ([temp.variadic]/6.7), and a function parameter pack is itself a pack
// expansion ([dcl.fct]/[temp.variadic]).  So when the parameter pack `t` is
// empty, the base initializer `Base(t...)` must instantiate as `Base()`.
//
// Compare [temp.variadic] Example 8:
//   template<class... T> void f(T... values) { X<T...> x(values...); }
//   template void f<>();   // OK: values... is an empty list, x{}
//
// KNOWN BUG: CBMC's empty-pack member-initializer removal keys off the pack
// TYPE name (here `T`), but this initializer mentions only the function
// parameter name `t`.  The empty function parameter `t` is dropped, yet the
// unexpanded `t...` survives in the initializer, so `t` resolves to nothing
// ("symbol 't' is unknown") and the initializer is discarded -- the base
// subobject is left uninitialised.  Note that the libstdc++ idiom
// `Base(std::forward<T>(t)...)` does NOT hit this, because it mentions the pack
// type `T` (via forward<T>), which the type-name-based removal catches.
//
// Flip to CORE once a function-parameter-pack expansion that is empty is
// reduced to an empty list regardless of whether it is written by parameter
// name or by pack type name.  Header-free and non-vacuous: assertion 2 is a
// deliberately wrong claim that must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

struct Base
{
  int tag;
  Base() : tag(7) {}
};

template <class... T>
struct Derived : Base
{
  Derived(const T &... t) : Base(t...) {} // T empty => Base(t...) is Base()
};

int main()
{
  Derived<> d; // empty parameter pack
  __CPROVER_assert(static_cast<Base &>(d).tag == 7, "empty-pack base initialized");
  __CPROVER_assert(static_cast<Base &>(d).tag == 0, "WRONG must FAIL");
  return 0;
}

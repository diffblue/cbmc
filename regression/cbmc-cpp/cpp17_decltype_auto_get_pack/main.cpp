// A function template with a DEDUCED return type (`decltype(auto)`) whose body
// expands a pack of REAL std::get calls into another call:
// `return add(std::get<I>(t)...)`.  This is the shape of libstdc++ std::apply's
// __apply_impl:
//   return std::__invoke(f, std::get<_Idx>(t)...);
//
// CORE (was KNOWNBUG): resolving `std::get<I>(t)` (with `I` a substituted
// non-type pack element, a constant) also considers the by-TYPE `std::get<T>`
// overloads; matching the constant against the TYPE parameter was a hard
// "unexpected cpp type: constant" error that aborted the whole overload
// resolution (including the viable by-index overload), so the return type was
// never deduced ("could not fully type-check").  Per N5008 [temp.arg]/2 +
// [temp.deduct]/8 it is a kind mismatch that removes just that candidate;
// fixed by extending the template-arg kind-mismatch machinery to a value
// (constant) in type position.
//
// The tuple is taken by reference, so this is independent of the separate
// std::get-by-value-copy value bug.  g++ compiles and runs r == 3; clang++
// accepts.  Non-vacuous: the result is a concrete function of the tuple
// elements selected by the deduced pack.

#include <tuple>

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

int add3(int a, int b, int c)
{
  return a + b + c;
}

template <class T, unsigned long... I>
decltype(auto) apply_impl(T &t, std::index_sequence<I...>)
{
  return add(std::get<I>(t)...);
}

template <class T, unsigned long... I>
decltype(auto) apply_impl3(T &t, std::index_sequence<I...>)
{
  return add3(std::get<I>(t)...);
}

int main()
{
  std::tuple<int, int> t{1, 2};
  int r = apply_impl(t, std::index_sequence<0, 1>{});
  __CPROVER_assert(r == 3, "decltype(auto) over std::get pack: 1+2==3");

  std::tuple<int, int, int> u{4, 5, 6};
  int s = apply_impl3(u, std::make_index_sequence<3>{});
  __CPROVER_assert(s == 15, "with make_index_sequence: 4+5+6==15");
  return 0;
}

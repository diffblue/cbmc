// N5008 [temp.inst]/2, [temp.deduct]: a constructor template of a class
// template instance, constrained by a SFINAE default template argument whose
// constexpr callee is a member function template of ANOTHER class template
// (instantiated over the class's pack) and whose body uses the callee's OWN
// parameter pack (sizeof...(Us)), must be instantiable when the enclosing
// class instance is constructed from a function template.  This is the shape
// of libstdc++ std::tuple's constrained constructors
// (_TupleConstraints<..., _Elements...>::__is_implicitly_constructible
// <_UElements...>() with `return __and_<...>::value` over its own pack),
// called from std::make_tuple -- the remaining blocker of cpp17_tuple_basic.
//
// KNOWNBUG: constructor overload resolution inside mk's instantiated body
// fails ("found no match for symbol 'tup'": the constrained constructor
// template is not a viable candidate -- observed in the real <tuple> as the
// forwarding constructor with an unexpanded `? &&` parameter), the failure is
// swallowed, mk gets no body, and its return value is nondeterministic.
// Direct construction in main works; the failure needs the constructor
// resolution to happen inside another function template's instantiated body.
// Each ingredient is necessary (verified by single-dimension toggling):
//   * the constexpr callee being a member of a second class template
//     (a free constexpr function template works),
//   * the callee's body referencing its OWN pack via sizeof...(Us)
//     (a body over only the class pack works),
//   * the construction site inside a function template (main works).
// g++ and clang++ accept and run this (assert holds).  Flip to CORE when the
// constrained constructor resolves.

extern "C" void __CPROVER_assert(int, const char *);

template<bool, typename T = void>
struct enable_if
{
};
template<typename T>
struct enable_if<true, T>
{
  typedef T type;
};
template<bool B, typename T = void>
using enable_if_t = typename enable_if<B, T>::type;

template<typename... Ts>
struct TCs
{
  template<typename... Us>
  static constexpr bool ok()
  {
    return sizeof...(Us) == 1;
  }
};

template<typename... Es>
struct tup
{
  int first;
  template<typename... Us,
           enable_if_t<TCs<Es...>::template ok<Us...>(), bool> = true>
  tup(Us &&... u) : first((int)(u, ...))
  {
  }
};

template<typename... Es>
tup<Es...> mk(Es... e)
{
  return tup<Es...>(e...);
}

int main()
{
  auto t = mk(5);
  __CPROVER_assert(t.first == 5, "constrained constructor forwards the value");
  return 0;
}

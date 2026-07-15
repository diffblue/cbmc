// N5008 [basic.scope.class]: the in-class initializer of a static data
// member is type-checked in the scope of the class, so it must resolve
// earlier-declared class-local typedefs (here the
// `typedef decltype(test<T>(0)) type;` feeding `value = type::value;` in the
// __is_swappable-style SFINAE probe).  g++ and clang++ evaluate both
// assertions below to true (runtime-verified).
//
// Was KNOWNBUG: cbmc type-checked the initializer mid-elaboration, where the
// class-local typedef was not yet resolvable; the failure was swallowed and
// the member's value silently left as a raw cpp_name, which read as nondet
// downstream -- both is_swappable<int> and is_swappable<NoCopy> mis-evaluated
// FALSE.  Fixed by deferring cpp_name-bearing static-member initializers to
// the end of the class and re-type-checking them in the class scope.
//
extern "C" void __CPROVER_assert(int, const char *);
template<typename _Tp, typename _Up = _Tp &&> _Up __declval(int);
template<typename _Tp> _Tp __declval(long);
template<typename _Tp> auto declval() noexcept -> decltype(__declval<_Tp>(0));
struct true_type { static const bool value = true; };
struct false_type { static const bool value = false; };

namespace stdx
{
template<typename T>
void swap(T &a, T &b)
{
  T tmp = a; a = b; b = tmp;
}
struct do_is_swappable
{
  template<typename T, typename = decltype(swap(declval<T &>(), declval<T &>()))>
  static true_type test(int);
  template<typename> static false_type test(...);
};
template<typename T>
struct is_swappable : do_is_swappable
{
  typedef decltype(test<T>(0)) type;
  static const bool value = type::value;
};
}

// swap's DECLARATION is viable for NoCopy (unevaluated probe succeeds), but
// its DEFINITION is ill-formed (deleted copy constructor); a conforming
// implementation never instantiates the definition ([temp.inst]/5).
struct NoCopy
{
  NoCopy() {}
  NoCopy(const NoCopy &) = delete;
  NoCopy &operator=(const NoCopy &) = delete;
};

int main()
{
  __CPROVER_assert(stdx::is_swappable<int>::value, "int swappable");
  __CPROVER_assert(
    stdx::is_swappable<NoCopy>::value,
    "probe checks the declaration only, not the definition");
  return 0;
}

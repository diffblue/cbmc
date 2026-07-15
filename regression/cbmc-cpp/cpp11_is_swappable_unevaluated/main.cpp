// N5008 [temp.inst]/5 + [expr.context]: an unevaluated operand (the
// decltype(swap(declval<T&>(), declval<T&>())) in the __is_swappable-style
// SFINAE probe) requires only the DECLARATION of the selected overload; the
// definition is not instantiated.  g++ and clang++ evaluate both assertions
// below to true (runtime-verified).
//
// KNOWNBUG: cbmc instantiates the swap DEFINITION from the unevaluated probe
// (observed on std::map as a collateral `std::swap<void>` instantiation whose
// void-typed local aborts the enclosing conversion -- the residual blocker of
// cpp20_map_basic / cpp11_map_insert after the drain-parity and out-of-line
// attachment fixes).  Here the definition for NoCopy is ill-formed (deleted
// copy), and its instantiation poisons the probe: both is_swappable<int> and
// is_swappable<NoCopy> mis-evaluate FALSE.  Flip to CORE once unevaluated
// operands stop instantiating definitions.
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

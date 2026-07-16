// N5008 [temp.arg.explicit] + [temp.deduct]/2 + [over.match.best]: a call
// `valid_args<Us...>()` that supplies only explicit template arguments to
// an OVERLOADED member function template must perform deduction/
// substitution per candidate and remove non-viable ones; with
// Us = {long, double, char} the pack overload
// `valid_args<typename, typename, typename...>` is viable (first two
// explicit arguments bind the fixed parameters, the rest the pack) and
// the single-parameter overload is not.
//
// KNOWNBUG: when such a call is the initializer of a DEFAULT TEMPLATE
// ARGUMENT of another member template (here `bool V` on the forwarding
// constructor -- exactly libstdc++ <tuple>'s
// `bool _Valid = __valid_args<_UElements...>()` shape), CBMC finds no
// viable overload; the constructor is removed and resolution fails
// ("found no match").  The same call made directly (not in a default
// template argument) resolves fine, and a NON-overloaded valid_args in
// the same default-argument position also works -- the broken ingredient
// is overload selection by explicit template arguments inside the
// default-template-argument context.  In real libstdc++ this silently
// drops tuple's perfect-forwarding constructors (masked whenever the
// `tuple(const _Elements&...)` constructor also matches).
//
// g++/clang++ accept and verify the value at runtime.  Flip to CORE when
// the default-template-argument evaluation resolves overloaded
// explicit-argument calls.
extern "C" void __CPROVER_assert(int, const char *);

template <typename T, typename U>
struct is_same_t
{
  static constexpr bool value = false;
};
template <typename T>
struct is_same_t<T, T>
{
  static constexpr bool value = true;
};
template <bool, typename T = void>
struct enable_if
{
};
template <typename T>
struct enable_if<true, T>
{
  typedef T type;
};

template <typename... Es>
struct Tup
{
  int v;
  // constraint overload for a single argument
  template <typename _Up>
  static constexpr bool valid_args()
  {
    return sizeof...(Es) == 1 && !is_same_t<Tup, _Up>::value;
  }
  // constraint overload for two or more arguments
  template <typename, typename, typename... _Tail>
  static constexpr bool valid_args()
  {
    return (sizeof...(_Tail) + 2) == sizeof...(Es);
  }
  // libstdc++ tuple's forwarding-constructor shape:
  // bool _Valid = __valid_args<_UElements...>()
  template <
    typename... Us,
    bool V = valid_args<Us...>(),
    typename enable_if<V, bool>::type = true>
  Tup(Us &&... u) : v((int)(u + ...))
  {
  }
};

int main()
{
  long a = 40;
  double b = 1.5;
  Tup<int, double, char> t3(a, b, (char)1);
  __CPROVER_assert(t3.v == 42, "three-arg forwarding ctor");

  long c = 42;
  Tup<int> t1(c);
  __CPROVER_assert(t1.v == 42, "one-arg forwarding ctor");
  return 0;
}

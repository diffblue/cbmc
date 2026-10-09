// N5008 [temp.deduct]/8: while matching an overloaded candidate, a
// template argument that fails to FORM (GCC 13's __and_fn chain: the
// pack expansion `__enable_if_t<_Bn::value>...` SFINAEs out, leaving a
// nil type in `_Requires<_Bn...>`) is a deduction failure that removes
// the candidate -- not a hard error ("missing type in template
// argument").  This is the shape of std::optional's two _Requires'd
// converting constructors (optional:754); the second must drop out for
// a non-convertible _Up.  Fixed for this copy-list-init shape; the
// same constructors on a class WITH a data member still fail (see
// cpp17_optional_requires_ctor_pair, KNOWNBUG).
// Reduced (cvise, clang-gated) from dog-fooding a TU including
// <util/std_code.h>.  g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

template <bool __v>
struct integral_constant
{
  static constexpr bool value = __v;
};
template <bool, typename>
struct enable_if;
template <typename _Tp>
struct enable_if<true, _Tp>
{
  typedef _Tp type;
};
template <bool _Cond, typename _Tp = void>
using __enable_if_t = typename enable_if<_Cond, _Tp>::type;
template <typename _Tp, typename...>
using __first_t = _Tp;
template <typename... _Bn>
auto __and_fn(int)
  -> __first_t<integral_constant<true>, __enable_if_t<_Bn::value>...>;
template <typename>
auto __and_fn(...) -> integral_constant<false>;
template <typename... _Bn>
struct __and_ : decltype(__and_fn<_Bn...>(0))
{
};
template <typename... _Bn>
constexpr bool __and_v = __and_<_Bn...>::value;
template <bool _Cond, typename _Tp>
using enable_if_t = typename enable_if<_Cond, _Tp>::type;
template <typename... _Cond>
using _Requires = enable_if_t<__and_v<_Cond...>, bool>;

struct optionalish
{
  template <typename _Up, _Requires<> = true>
  optionalish(_Up &&)
  {
  }
  template <typename _Up, _Requires<_Up> = false>
  optionalish(_Up &&)
  {
  }
};

struct exprt
{
  int op;
  exprt op1()
  {
    return {op + 1};
  }
  optionalish initial_value()
  {
    return {op1()}; // considers both ctors; the second must SFINAE out
  }
};

int main()
{
  // initial_value() itself is not called: constructing the returned
  // optionalish trips a PRE-EXISTING symex crash recorded in
  // cpp17_optional_requires_ctor_pair (KNOWNBUG).  Converting its body
  // is what this test pins: before the fix the whole TU failed with
  // CONVERSION ERROR at the _Requires deduction.
  exprt e{7};
  __CPROVER_assert(e.op1().op == 8, "conversion completed; op1 has a body");
  return 0;
}

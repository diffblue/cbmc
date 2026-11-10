// Distilled residual layer of cpp17_optional_requires_ctor_pair: the
// SFINAE'd constructor pair works when the pack expansion spells
// `typename enable_if<_Bn::value, void>::type...` directly, but with
// the ALIAS-WITH-DEFAULTED-PARAMETER form `__enable_if_t<_Bn::value>
// ...` ([temp.alias], the defaulted _Tp = void) the deduction fails
// and main is silently dropped (0 properties; vacuous SUCCESS caught
// by this desc).  g++/clang++ accept and verify at runtime.
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
  int selected;
  template <typename _Up, _Requires<> = true>
  optionalish(_Up &&) : selected(1)
  {
  }
  template <typename _Up, _Requires<_Up> = false>
  optionalish(_Up &&) : selected(2)
  {
  }
};

struct exprt
{
  int op;
};

int main()
{
  exprt e{7};
  optionalish o(e); // direct-init: first candidate must win
  __CPROVER_assert(o.selected == 1, "SFINAE'd candidate dropped");
  return 0;
}

// N5008 [temp.deduct.call] + [dcl.fct]/2 (trailing-return-type) +
// [temp.variadic]/5: a free function template with a trailing return type
// `-> decltype(::new((void*)0) _Tp(declval<_Args>()...))` -- the C++20
// std::construct_at declaration ([specialized.construct]) -- must deduce
// _Tp and the _Args pack from the call arguments and then form the return
// type, so the call resolves.
//
// Was KNOWNBUG: with two or more call arguments constructing a
// class-template instance, deduction of `construct_at` failed ("found no
// match") because the trailing-return `decltype` over the pack-expanded
// placement-new was not expanded during argument deduction.  Fixed by
// treating a cpp_new initializer's expression-list as a pack-expansion
// context in template_mapt::expand_call_argument_packs.  g++/clang++
// runtime-verified.
extern "C" void __CPROVER_assert(int, const char *);

template <typename T>
struct remove_reference
{
  typedef T type;
};
template <typename T>
struct remove_reference<T &>
{
  typedef T type;
};
template <typename T>
struct remove_reference<T &&>
{
  typedef T type;
};
template <typename _Tp>
constexpr _Tp &&forward(typename remove_reference<_Tp>::type &__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}
template <typename _Tp>
constexpr _Tp &&forward(typename remove_reference<_Tp>::type &&__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}
template <typename _Tp>
_Tp &&declval() noexcept;

void *operator new(unsigned long, void *p)
{
  return p;
}

struct pc_t
{
};
template <typename... E>
struct tuple
{
};
template <>
struct tuple<int &&>
{
  int v;
  tuple(int &&x) : v(x)
  {
  }
};

template <typename T1, typename T2>
struct pair
{
  T1 first;
  T2 second;
  pair() : first(), second()
  {
  }
  template <typename... A1, typename... A2>
  pair(pc_t, tuple<A1...> t1, tuple<A2...>) : first(t1.v), second(sizeof...(A1))
  {
  }
};

// the C++20 std::construct_at declaration shape: trailing return type is a
// decltype over the pack-expanded placement-new
template <typename _Tp, typename... _Args>
auto construct_at(_Tp *__location, _Args &&...__args)
  -> decltype(::new((void *)0) _Tp(declval<_Args>()...))
{
  return ::new((void *)__location) _Tp(forward<_Args>(__args)...);
}

int main()
{
  pair<const int, int> p;
  int x = 4;
  tuple<int &&> t1(static_cast<int &&>(x));
  tuple<> t2;
  construct_at(&p, pc_t{}, t1, t2);
  __CPROVER_assert(
    p.first == 4 && p.second == 1, "decltype-return construct_at");
  return 0;
}

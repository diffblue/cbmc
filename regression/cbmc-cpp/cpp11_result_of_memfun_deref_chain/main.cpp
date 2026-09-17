extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>
#include <utility>
struct S { int k; int mul(int a) const { return k * a; } int mul2(int a) { return k * a; } };
typedef int (S::*PMF)(int) const;
typedef int (S::*PMF2)(int);
template <class T> struct success { typedef T type; };
struct failure {};
struct deref_impl
{
  template <class _Fp, class _Tp1, class... _Args1>
  static success<decltype(((*std::declval<_Tp1>()).*std::declval<_Fp>())(std::declval<_Args1>()...))> _S_test(int);
  template <class...> static failure _S_test(...);
};
template <class _MemPtr, class _Arg, class... _Args>
struct deref : private deref_impl
{
  typedef decltype(_S_test<_MemPtr, _Arg, _Args...>(0)) type;
};
template <class _MemPtr, class _Arg, class... _Args> struct memfun;
template <class _Res, class _Class, class _Arg, class... _Args>
struct memfun<_Res _Class::*, _Arg, _Args...>
{
  typedef _Res _Class::*_MemPtr;
  typedef typename deref<_MemPtr, _Arg, _Args...>::type type;
};
int main()
{
  deref<PMF, S *&, int &&>::type::type r0 = 0;
  __CPROVER_assert(r0 == 0, "deref via private base _S_test");
  memfun<PMF2, S *&, int &&>::type::type r2 = 2;
  __CPROVER_assert(r2 == 2, "memfun partial spec _Res _Class::* (non-const)");
  memfun<PMF, S *&, int &&>::type::type r1 = 1;
  __CPROVER_assert(r1 == 1, "memfun partial spec _Res _Class::* (const)");
  return 0;
}

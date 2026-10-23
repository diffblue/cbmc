// GCC 14's builtin traits __is_invocable, __is_nothrow_invocable and
// __array_rank, which libstdc++ 16 uses for std::is_invocable,
// std::is_nothrow_invocable and std::rank (`__bool_constant<__is_invocable(
// _Fn, _ArgTypes...)>').  N5008 [meta.rel]/6-7, [func.require]/1: INVOKE
// with declval'd operands must be well-formed -- a call, or a pointer to
// member applied to the first argument.  __is_nothrow_invocable is treated
// as __is_invocable (the front end does not model exception
// specifications).  Header-free; g++ >= 15 accepts the builtins.
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int f(int) const;
  int m;
  void operator()(double);
};
struct NotCallable
{
};
struct NS
{
  void operator()(double) noexcept;
};
int g(int, char);
template <typename F, typename... A>
struct inv
{
  static constexpr bool value = __is_invocable(F, A...);
};
template <typename F, typename... A>
struct ninv
{
  static constexpr bool value = __is_nothrow_invocable(F, A...);
};
int main()
{
  __CPROVER_assert(inv<S, double>::value, "functor");
  __CPROVER_assert(inv<S &, int>::value, "functor lvalue, int -> double");
  __CPROVER_assert(!inv<S>::value, "functor needs an argument");
  __CPROVER_assert(!inv<S, int, int>::value, "functor too many args");
  __CPROVER_assert(!inv<NotCallable, int>::value, "no operator()");
  __CPROVER_assert(inv<int (*)(int, char), int, char>::value, "fn ptr");
  __CPROVER_assert(inv<decltype(g), int, char>::value, "fn type");
  __CPROVER_assert(!inv<int (*)(int, char), int>::value, "fn ptr arity");
  __CPROVER_assert(inv<int (S::*)(int) const, S, int>::value, "memfn obj");
  __CPROVER_assert(inv<int (S::*)(int) const, S *, int>::value, "memfn ptr");
  __CPROVER_assert(
    inv<int (S::*)(int) const, const S &, int>::value, "memfn cref");
  __CPROVER_assert(!inv<int (S::*)(int) const, S>::value, "memfn missing arg");
  __CPROVER_assert(inv<int S::*, S>::value, "data member");
  __CPROVER_assert(inv<int S::*, S &>::value, "data member ref");
  __CPROVER_assert(!inv<int S::*, S, int>::value, "data member extra arg");
  __CPROVER_assert(!inv<int, int>::value, "int is not callable");
  __CPROVER_assert(ninv<NS, double>::value, "nothrow form");
  __CPROVER_assert(
    !ninv<NotCallable, int>::value, "nothrow form, no operator()");
  __CPROVER_assert(__array_rank(int) == 0, "rank 0");
  __CPROVER_assert(__array_rank(int[3]) == 1, "rank 1");
  __CPROVER_assert(__array_rank(int[3][4][5]) == 3, "rank 3");
  __CPROVER_assert(__array_rank(int[][2]) == 2, "rank unbounded");
  return 0;
}

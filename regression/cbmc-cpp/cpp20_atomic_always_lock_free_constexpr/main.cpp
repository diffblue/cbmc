// N5008 [expr.const] + [temp.arg.nontype]: a template argument must be
// a converted constant expression; GCC/clang's builtin
// __atomic_always_lock_free(size, ptr) is a constant expression when
// its arguments are.  CBMC folds it in a RUNTIME read (a plain assert
// on lock_free<T>::value works) but not when the value is needed in a
// CONSTANT-EXPRESSION context -- here as the first argument of a
// conditional alias -- failing with "expected constant expression" and
// cascading into "symbol ... is unknown" for every dependent alias.
// This is libc++ <atomic>'s __libcpp_is_always_lock_free /
// __contention_t_or_largest shape (aliases.h), one of the two
// remaining blockers of cpp20_ranges_basic_libcxx.
extern "C" void __CPROVER_assert(bool, const char *);
template <bool, class T, class F> struct conditional_
{
  using type = T;
};
template <class T, class F> struct conditional_<false, T, F>
{
  using type = F;
};
template <bool B, class T, class F>
using conditional_t_ = typename conditional_<B, T, F>::type;
template <class T> struct lock_free
{
  static const bool value = __atomic_always_lock_free(sizeof(T), nullptr);
};
using contention_t = long long;
using pick = conditional_t_<lock_free<contention_t>::value, contention_t, int>;
int main()
{
  __CPROVER_assert(sizeof(pick) == sizeof(long long), "alias picks lock-free type");
  return 0;
}

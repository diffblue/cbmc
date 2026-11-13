// N5008 [meta.rel]/2: is_nothrow_invocable<Fn, Args...> holds if
// is_invocable does and the INVOKE expression is known not to throw
// ([expr.unary.noexcept]).  libstdc++ 16 implements it by GCC's builtin
// __is_nothrow_invocable, which the front end evaluated as
// __is_invocable.  std::unordered_map then did not cache the hash code of
// a key whose hash may throw (__cache_default), and the static_assert of
// ~_Hashtable on the bucket index failed (ignored with a warning).
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);
struct throwing
{
  int operator()(int x) const
  {
    return x;
  }
};
struct nonthrowing
{
  int operator()(int x) const noexcept
  {
    return x;
  }
};
int main()
{
  __CPROVER_assert(
    !std::is_nothrow_invocable_v<const throwing &, int>, "may throw");
  __CPROVER_assert(
    std::is_nothrow_invocable_v<const nonthrowing &, int>, "does not throw");
  __CPROVER_assert(std::is_invocable_v<const throwing &, int>, "invocable");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

// N5008 [meta.unary.prop] Table 54: is_nothrow_constructible<T, Args...>
// holds if is_constructible<T, Args...> does and the variable definition
// `T t(declval<Args>()...);' is known not to throw any exceptions
// ([expr.unary.noexcept]); is_nothrow_copy_constructible<T> is
// is_nothrow_constructible<T, const T &>.
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);

struct CopyThrows
{
  CopyThrows()
  {
  }
  CopyThrows(const CopyThrows &)
  {
  }
};
struct FromInt
{
  FromInt(int) noexcept
  {
  }
  FromInt(long)
  {
  }
};

int main()
{
  __CPROVER_assert(
    !std::is_nothrow_copy_constructible<CopyThrows>::value, "copy throws");
  __CPROVER_assert(
    std::is_nothrow_constructible<FromInt, int>::value, "noexcept(int)");
  __CPROVER_assert(
    !std::is_nothrow_constructible<FromInt, long>::value, "throwing (long)");
  __CPROVER_assert(
    std::is_nothrow_constructible<FromInt, long>::value, "WRONG (must FAIL)");
  return 0;
}

// N5008 [except.spec]/12.3, [conv.fctptr]: the type of &W<int>::f is
// `void (*)()', so overload resolution selects is_nothrow_fp(void (*)()).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct W
{
  static void f() noexcept(sizeof(T) == 1)
  {
  }
};
template <class T>
constexpr bool is_nothrow_fp(void (*)() noexcept)
{
  return true;
}
template <class T>
constexpr bool is_nothrow_fp(void (*)())
{
  return false;
}
int main()
{
  __CPROVER_assert(is_nothrow_fp<int>(&W<char>::f), "noexcept(true) member");
  __CPROVER_assert(!is_nothrow_fp<int>(&W<int>::f), "noexcept(false) member");
  __CPROVER_assert(is_nothrow_fp<int>(&W<int>::f), "WRONG (must FAIL)");
}

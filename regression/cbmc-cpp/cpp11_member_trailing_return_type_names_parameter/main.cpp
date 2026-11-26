extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [basic.scope.param]/1, [dcl.fct]/1: a parameter's scope extends to
// the end of its declarator, so a member's trailing return type names the
// parameters (the MSVC STL's _Invoker1::_Call, behind is_invocable)
struct plain
{
  static auto call(int obj) -> decltype(obj)
  {
    return obj + 1;
  }
};
template <class C>
struct invoker
{
  static auto call(C obj) -> decltype(obj)
  {
    return obj;
  }
  auto twice(C obj) const -> decltype(obj + obj)
  {
    return obj + obj;
  }
};
template <class>
using void_t = void;
template <class C, class = void>
struct invocable
{
  static constexpr bool value = false;
};
template <class C>
struct invocable<C, void_t<decltype(invoker<C>::call(C()))>>
{
  static constexpr bool value = true;
};
int main()
{
  decltype(plain::call(1)) a = plain::call(1);
  decltype(invoker<long>::call(2)) b = invoker<long>::call(2);
  __CPROVER_assert(a == 2 && b == 2 && sizeof(b) == sizeof(long), "calls");
  __CPROVER_assert(invoker<int>{}.twice(3) == 6, "member");
  __CPROVER_assert(invocable<int>::value, "partial specialization");
  __CPROVER_assert(!invocable<int>::value, "WRONG (must FAIL)");
  return 0;
}

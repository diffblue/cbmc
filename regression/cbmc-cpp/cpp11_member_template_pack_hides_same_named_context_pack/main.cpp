extern "C" void __CPROVER_assert(bool, const char *);
template <class... V>
struct at_impl
{
  template <class T, class... Ts>
  static T eval(V..., T *, Ts *...);
};
// N5008 [basic.scope.temp]/2, [temp.deduct.call]/1: the pack Ts of the
// called member template is deduced from the call; the same-named pack of
// the class template that names the call is a different entity (the MSVC
// STL's _Meta_at_ calls _Meta_at_impl<...>::_Eval<_Ty, _Types...>)
template <class... Ts>
struct Y
{
  using type =
    decltype(at_impl<void *>::eval(nullptr, (long *)nullptr, (char *)nullptr));
};
int main()
{
  __CPROVER_assert(
    sizeof(Y<char, char, char>::type) == sizeof(long), "T deduced as long");
  __CPROVER_assert(sizeof(Y<char, char, char>::type) == 1, "WRONG (must FAIL)");
  return 0;
}

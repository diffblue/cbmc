extern "C" void __CPROVER_assert(bool, const char *);
template <class... _Args>
auto sum(_Args... __x) -> decltype((__x + ... + 0))
{
  return (__x + ... + 0);
}
int main()
{
  __CPROVER_assert(sum(2, 3) == 5, "two-element fold in trailing decltype");
  return 0;
}

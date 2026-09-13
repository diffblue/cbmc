extern "C" void __CPROVER_assert(bool, const char *);
template <class... _Args>
auto wrap(_Args... __x) -> decltype((__x + ... + 0))
{
  return (__x + ... + 0);
}
int main()
{
  __CPROVER_assert(wrap(5) == 5, "bare fold in trailing decltype");
  return 0;
}

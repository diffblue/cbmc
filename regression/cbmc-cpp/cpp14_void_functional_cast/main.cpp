extern "C" void __CPROVER_assert(bool, const char *);
int calls = 0;
void f()
{
  ++calls;
  return void();
}
auto g()
{
  ++calls;
  return void();
}
template <class T>
T make()
{
  return T();
}
int main()
{
  f();
  g();
  void();
  (void)0;
  make<void>();
  __CPROVER_assert(calls == 2, "void() performs no initialization");
  __CPROVER_assert(calls == 3, "WRONG (must FAIL)");
}

// C++14 generic lambda
int main()
{
  auto identity = [](auto x) { return x; };
  int r = identity(42);
  __CPROVER_assert(r == 42, "generic lambda");
  return 0;
}

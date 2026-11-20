// N5008 [dcl.spec.auto], [dcl.type.decltype]: auto and decltype deduce int.
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto x = 3;
  decltype(x) y = x + 1;
  __CPROVER_assert(y == 4, "auto and decltype");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

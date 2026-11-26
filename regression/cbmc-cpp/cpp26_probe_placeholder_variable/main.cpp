// N5008 [basic.scope.scope]: two variables named _ in one scope (name-
// independent declarations).
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int _ = 1;
  int _ = 2;
  __CPROVER_assert(true, "two placeholder variables");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

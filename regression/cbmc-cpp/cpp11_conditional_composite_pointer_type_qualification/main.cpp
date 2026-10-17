extern "C" void __CPROVER_assert(bool, const char *);
int which(int *)
{
  return 1;
}
int which(const int *)
{
  return 2;
}
int main()
{
  int x = 5;
  int *p = &x;
  const int *cp = &x;
  bool b = true;
  // N5008 [expr.cond]/7.3, [expr.type]/4: the composite pointer type of
  // int * and const int * is const int *
  __CPROVER_assert(which(b ? p : cp) == 2, "composite pointer type");
  __CPROVER_assert(*(b ? p : cp) == 5, "value");
  __CPROVER_assert(which(b ? p : cp) == 1, "WRONG (must FAIL)");
  return 0;
}

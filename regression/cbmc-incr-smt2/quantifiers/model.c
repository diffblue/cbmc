int main()
{
  int c[2];
  c[0] = 0;
  c[1] = 1;
  // clang-format off
  __CPROVER_assert(__CPROVER_exists { int i; (i >= 0 && i < 2) && c[i] == 1 }, "holds");
  // clang-format on
  __CPROVER_assert(c[0] == 1, "fails");
  return 0;
}

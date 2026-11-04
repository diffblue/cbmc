int main()
{
  double d;
  float f;
  __CPROVER_assume(d == -2.5 && f == 1.25f);
  __CPROVER_assert(0, "show");
  return 0;
}

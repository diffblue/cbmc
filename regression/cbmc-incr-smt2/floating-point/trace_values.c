int main()
{
  float x;
  __CPROVER_assume(x == 2.0f);
  double d;
  __CPROVER_assume(d == -0.5);
  __CPROVER_assert(x != 2.0f || d != -0.5, "values");
  return 0;
}

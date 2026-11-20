int main()
{
  float x, y;
  __CPROVER_assume(x == 1.5f && y == -0.25f);
  __CPROVER_assert(x + y == 1.25f, "plus");

  int i;
  __CPROVER_assume(i == -7);
  __CPROVER_assert((float)i == -7.0f, "from negative int");

  float a;
  __CPROVER_assume(a >= 1.0f && a <= 2.0f);
  float s = a + 1.0f;
  __CPROVER_assert(s != 3.0f, "sum can be 3");
  return 0;
}

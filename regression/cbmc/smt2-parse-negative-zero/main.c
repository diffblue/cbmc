int main(void)
{
  float x;
  __CPROVER_assume(x == 0.0f && __builtin_signbit(x));
  double y;
  __CPROVER_assume(y == 0.0 && __builtin_signbit(y));
  __CPROVER_assert(0, "show");
}

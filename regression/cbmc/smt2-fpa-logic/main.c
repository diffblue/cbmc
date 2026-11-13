int main()
{
  float x;
  __CPROVER_assume(x == x);
  float y = x * 2.0f;
  __CPROVER_assert(y != 3.0f, "can be 3");
  return 0;
}

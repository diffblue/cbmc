int main()
{
  float f = 1.0;
  __CPROVER_assert(f + 0.5f == 1.5f, "addition");
  return 0;
}

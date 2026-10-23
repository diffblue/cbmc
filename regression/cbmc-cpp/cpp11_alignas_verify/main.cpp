// C++11 alignof
int main()
{
  __CPROVER_assert(alignof(int) == 4, "int alignment");
  __CPROVER_assert(alignof(double) == 8, "double alignment");
  return 0;
}

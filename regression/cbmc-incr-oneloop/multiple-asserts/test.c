int main()
{
  for(int i = 0; i < 10; ++i)
  {
    __CPROVER_assert(i != 5, "assertion i != 5");
    __CPROVER_assert(i != 8, "assertion i != 8");
  }
  return 0;
}

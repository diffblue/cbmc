int main()
{
  unsigned i = 10;
  while(i != 0)
    // clang-format off
    __CPROVER_decreases(i)
    // clang-format on
    {
      i--;
    }

  return 0;
}

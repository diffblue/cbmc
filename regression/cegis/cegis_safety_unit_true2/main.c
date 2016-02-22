int main(void)
{
  int x;
  while (x < 2)
    ++x;
  __CPROVER_assert(x >= 2, "A");
  return 0;
}

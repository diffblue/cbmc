int main(void)
{
  int x = 0;
  while (x < 2)
    ++x;
  __CPROVER_assert(x == 4, "A");
  return 0;
}

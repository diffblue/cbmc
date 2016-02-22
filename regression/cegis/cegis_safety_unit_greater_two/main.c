int main(void)
{
  int x, y;
  if (x > 2)
    x = 2;

  y=0;
  while (x < 2)
    ++x;
  __CPROVER_assert(x == 2, "A");
  return 0;
}

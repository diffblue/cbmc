int main(void)
{
  int x;
  int y;
  int z=0;
  while (x != 99 && y != 508)
    ++z;

  __CPROVER_assert(y != 508, "A");
  return 0;
}

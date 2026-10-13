int main()
{
  unsigned x;
  __CPROVER_assert(x + 1 != 0 || x == 0xffffffffu, "p");
  return 0;
}

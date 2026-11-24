int main()
{
  int i = 0;
  while(i < 10)
    __CPROVER_loop_invariant(i == 0)
    {
      i++;
    }
  int x = 2147483647 + i;
  return x;
}

int main()
{
  int x;
  goto label;
  x = 2;
label:
  while(x < 5)
    __CPROVER_loop_invariant(x <= 5)
    {
      x++;
    }
}

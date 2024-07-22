int main()
{
  unsigned i;

  while(i > 1)
    __CPROVER_loop_invariant(({
      unsigned b = i >= 1;
      goto label;
      b = i < 1;
    label:
      b;
    }))
    {
      i--;
    }
}

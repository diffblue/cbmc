static void foo()
{
  unsigned i;

  for(i = 0; i < 16; i++)
    __CPROVER_loop_invariant(1 == 1)
    {
      int v = 1;
    }
}

static void bar()
{
  unsigned i;

  for(i = 0; i < 16; i++)
    __CPROVER_loop_invariant(1 == 1)
    {
      int v = 1;
    }
}

int main()
{
  bar();
  foo();
  foo();
}

int foo()
{
  int x = 0;
  while(x < 10)
  {
    ++x;
  }
  return x;
}

int main()
{
  int x = 0;

  for(int i = 0; i < 10; ++i)
    __CPROVER_loop_invariant(0 <= x && x <= 10)
    {
      if(x < 10)
        x++;
    }

  x += foo();

  __CPROVER_assert(x <= 20, "");
}

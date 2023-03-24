#define N 10

int foo(int i);

int main()
{
  int i = 0;
  while(i != N)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= N) 
    __CPROVER_decreases(foo(i))
    // clang-format on
    {
      i++;
    }

  return 0;
}

int foo(int i)
{
  return N - i;
}

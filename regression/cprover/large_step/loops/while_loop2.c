int nondet_int();

int main()
{
  int N = nondet_int();
  int x = 0;
  while(x < N)
    x++;

  __CPROVER_assert(x == N, "property 1"); // fails
}

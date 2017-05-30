int main()
{
  unsigned size;
  char array[size];

  for(unsigned i = 0; i < N; i++)
    __CPROVER_assume(array[i] == 123);

  __CPROVER_assert(0, "");
}

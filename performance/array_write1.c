int main()
{
  unsigned size;
  char array[size];

  for(unsigned i = 0; i < N; i++)
    array[i] = 123;

  __CPROVER_assert(0, "");
}

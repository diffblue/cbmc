int nondet_int();

int main()
{
  int i;
  int array[2];

  for(i = 0; i < 2; i++)
    array[i] = nondet_int();

  __CPROVER_assert(array[0] == array[1], "property 1"); // fails
}

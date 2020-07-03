static int array[2];

void main(void)
{
  int i;

  for(i = 0; i < 1; i++)
    array[i] = 5;

  __CPROVER_assert(array[0] == 5, "array[0] == 5");
  __CPROVER_assert(array[1] == 5, "array[1] == 5");
}

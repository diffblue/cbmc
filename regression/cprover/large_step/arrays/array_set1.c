int array[10];

int main()
{
  __CPROVER_array_set(array, 123);
  __CPROVER_assert(array[5l] == 123, "property 1"); // passes
  return 0;
}

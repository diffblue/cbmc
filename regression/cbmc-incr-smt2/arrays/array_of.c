int main()
{
  int example_array[10000];
  unsigned int index;
  __CPROVER_assume(index < 999);

  __CPROVER_array_set(example_array, 43);
  __CPROVER_assert(example_array[index] != 43, "False array condition");

  __CPROVER_array_set(example_array, 42);
  __CPROVER_assert(example_array[index] == 42, "Valid array condition");
}

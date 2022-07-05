int main()
{
  int example_array[] = {5, 4, 3, 2, 1};
  unsigned int index;
  __CPROVER_assume(index < 5);
  __CPROVER_assert(example_array[index] != 42, "Non-existent element");
  __CPROVER_assert(example_array[index] != 5, "Index 0");
  __CPROVER_assert(example_array[index] != 4, "Index 1");
  __CPROVER_assert(example_array[index] != 3, "Index 2");
  __CPROVER_assert(example_array[index] != 2, "Index 3");
  __CPROVER_assert(example_array[index] != 1, "Index 4");
  __CPROVER_assert(example_array[index] == 5 - index, "Index value relation");
}

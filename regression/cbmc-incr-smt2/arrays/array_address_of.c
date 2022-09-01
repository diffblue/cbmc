int main()
{
  int example_array[10000];
  __CPROVER_assert(
    __CPROVER_OBJECT_SIZE(example_array) == 40000, "Array condition 1");
  __CPROVER_assert(
    __CPROVER_OBJECT_SIZE(example_array) == 40001, "Array condition 2");
}

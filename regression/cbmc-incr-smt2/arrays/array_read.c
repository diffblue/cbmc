int main()
{
  int example_array[10000];
  unsigned int index;
  __CPROVER_assume(index < 10000);
  __CPROVER_assert(example_array[index] != 42, "Array condition");
}

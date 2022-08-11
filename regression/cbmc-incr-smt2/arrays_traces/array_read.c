int main()
{
  int example_array[1025];
  unsigned int index;
  __CPROVER_assume(index < 1025);
  __CPROVER_assert(example_array[index] != 42, "Array condition");
}

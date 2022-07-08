int main()
{
  int example_array[10000][2000];
  unsigned int index_i;
  unsigned int index_j;
  __CPROVER_assume(index_i < 10000);
  __CPROVER_assume(index_j < 2000);
  example_array[index_i][index_j] = 42;
  __CPROVER_assert(example_array[index_i][index_j] == 42, "Array condition");
  __CPROVER_assert(example_array[index_i][index_j] != 42, "Array condition");
}

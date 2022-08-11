int main()
{
  int example_array[100][200];
  unsigned int index_i;
  unsigned int index_j;
  __CPROVER_assume(index_i < 100);
  __CPROVER_assume(index_j < 200);
  __CPROVER_assert(example_array[index_i][index_j] != 42, "Array condition");
}

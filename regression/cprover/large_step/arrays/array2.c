int main()
{
  int array[10];
  int i, j, k;
  __CPROVER_assume(i == j);
  __CPROVER_assert(array[i] == array[j], "property 1"); // passes
  __CPROVER_assert(array[i] == array[k], "property 2"); // fails
}

int array[10] = {0, 1, 2, 3, 4};

int main()
{
  __CPROVER_assert(array[0l] == 0, "property 1"); // passes
  __CPROVER_assert(array[1l] == 1, "property 2"); // passes
  return 0;
}

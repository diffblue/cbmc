int global;

int main()
{
  int array[100];
  int *x = array;
  *(x + 2) = 123;
  __CPROVER_assert(0, "property 1");
}

int array[10];

int main()
{
  array[1l] = 10;
  array[2l] = 20;
  __CPROVER_assert(array[1l] == 10, "property 1"); // passes
  __CPROVER_assert(array[2l] == 20, "property 2"); // passes
  __CPROVER_assert(array[2l] == 30, "property 3"); // fails
}

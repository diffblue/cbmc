int *nondet_pointer();

int main()
{
  int some_array[10];
  int *p = some_array;
  int *q = nondet_pointer();
  int index;

  __CPROVER_assume(index >= 0 && index < 10);
  __CPROVER_assume(q == p);

  q[index] = 123;

  __CPROVER_assert(some_array[index] == 123, "value of array[index]");

  return 0;
}

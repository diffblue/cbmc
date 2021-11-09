int *nondet_pointer();

int main()
{
  int x = 123;
  int *p = &x;
  int *q = nondet_pointer();

  if(p == q)
    __CPROVER_assert(*q == 123, "value of *q");

  return 0;
}

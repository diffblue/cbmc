int *nondet_pointer();

int main()
{
  int x = 123;
  int *p = &x;
  int *q = nondet_pointer();
  int *r;

  if(p == q)
    __CPROVER_assert(*q == 123, "value of *q");

  if(p == r)
    __CPROVER_assert(*r == 123, "value of *q");

  return 0;
}

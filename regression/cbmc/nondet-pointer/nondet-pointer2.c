int *nondet_pointer();

int main()
{
  int x = 123, y = 456;
  int *px = &x;
  int *py = &y;
  int *q = nondet_pointer();

  if(q == px || q == py)
    __CPROVER_assert(*q == 123 || *q == 456, "value of *q");

  return 0;
}

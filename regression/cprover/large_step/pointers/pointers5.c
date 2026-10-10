int x;

int main()
{
  int *p, *q;

  __CPROVER_assume(p == q);
  __CPROVER_assert(*p == *q, "property 1"); // passes

  return 0;
}

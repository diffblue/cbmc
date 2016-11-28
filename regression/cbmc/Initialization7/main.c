struct S
{
  int *s;
};

int nondet_int();

int main()
{
  int x=nondet_int();

  struct S p;
  if(p.s!=0)
    p.s=&x;

  *(p.s)=42;

  // should fail, as p.s may be null
  __CPROVER_assert(x==42, "");

  return 0;
}

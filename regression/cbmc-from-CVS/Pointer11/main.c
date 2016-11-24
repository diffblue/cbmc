int nondet_int();

struct S
{
  int a, b;
};

main()
{
  struct S s[10];
  int *p, *q, x=nondet_int(), y=nondet_int();
  
  __CPROVER_assume(x==0);
  __CPROVER_assume(y==0);
  
  p=&(s[x].a);
  q=&(s[y].a);
  
  assert(p==q);
}

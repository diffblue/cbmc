struct S
{
  int *s;
};

int main()
{
  int x=nondet_int();
  struct S p;
  if(p.s!=0)
  {
    p.s=&x;
  }
  *(p.s)=42;
  __CPROVER_assert(x==42, "");
  return 0;
}

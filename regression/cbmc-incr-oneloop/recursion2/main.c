int foo(int x)
{
  if(x<10) return foo(x+1);
  return x;
}

int main()
{
  int x;
  __CPROVER_assume(x==0);
  assert(foo(x)==10);
}

int main()
{
  int * a;
  int b=1;
  __CPROVER_assume(a == &b);
  assert(*a==1);
  return 0;
}

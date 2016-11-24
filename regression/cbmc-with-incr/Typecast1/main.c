int main()
{
  assert(((long long int)(unsigned long long)-1)==-1);

  int a;
  __CPROVER_assume(a==-1);
  unsigned long long x = (unsigned long long) a;
  assert(x == -1);
  return 0;
}

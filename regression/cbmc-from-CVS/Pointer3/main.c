int main()
{
  typedef int *intptr;
  intptr a[10];
  int x, y;
  
  unsigned i;
  __CPROVER_assume(i<10);

  a[i]=&x;
  a[5]=&y;
  
  assert(*(a[i])==x);  
}

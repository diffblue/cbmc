int main()
{
  unsigned int *p=(unsigned int *)0xdeadbeef;
  assert(p!=0);

  int zero;  
  __CPROVER_assume(zero==0);
  unsigned int *q=(unsigned int *)zero;
  assert(q==0);
}

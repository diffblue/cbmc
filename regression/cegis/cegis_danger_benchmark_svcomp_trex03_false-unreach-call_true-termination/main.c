int main(void) {
  unsigned int x1;
  unsigned int x2;
  unsigned int x3;
  unsigned int d1=1;
  unsigned int d2=1;
  unsigned int d3=1;

  int c1;
  int c2;

  while(x1>0 && x2>0 && x3>0)
  {
    if (c1) x1=x1-d1;
    else if (c2) x2=x2-d2;
    else x3=x3-d3;
    int nondet_0;
    c1=nondet_0;
    int nondet_1;
    c2=nondet_1;
  }

  __CPROVER_assert(x1==0 && x2==0 && x3==0, "A");

  return 0;
}

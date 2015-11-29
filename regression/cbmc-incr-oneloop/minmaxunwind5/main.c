extern int nondet_int();
int main()
{
  int x = nondet_int();
  __CPROVER_assume(0<=x && x<=1);
  while(x<10) {
    int i=-10;
    for(;i<1;i++);
    x=x+i;
    assert(x<6);
  }
}

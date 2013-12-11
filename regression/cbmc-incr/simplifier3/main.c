extern int nondet();
int main()
{
  int x;
  __CPROVER_assume(0<=x && x<=1);
  while(x<3) {
    x++;
    assert(x<=3);
  }
}

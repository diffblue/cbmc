int main()
{
  int x;
  __CPROVER_assume(0<=x && x<=1);
  int y;
  __CPROVER_assume(0<=y && y<=1);
  while(1) {
    switch(x) {
    case 0 : x++; y++; break;
    case 1 : x++; break;
    case 2 : if(y>10) x=10; else x++; break;
    default: break;
    }
    assert(x<=4);
  }
}

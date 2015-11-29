extern int nondet();
int main()
{
  int x = 0;
  int y;
  __CPROVER_assume(0<=y && y<=1);
  while(1) {
    switch(x) {
    case 0 : 
      if(y<=2) {
        if(nondet()) x=1; 
        else y++;
      }
      else x=2;
      break;
    case 1 : x=3; break;
    case 2 : x=3; break;
    case 3 : if(y<5) y++; break;
    default: break;
    }
    assert(x<=3 && y<=5);
  }
}

// switch in switch

int f(int j)
{
  switch(j)
  {
  case 3:
    return 4;
  
  default:
    return 5;
  }
}

int main()
{
  int i;
  
  __CPROVER_assume(i==3 || i==4);
  
  switch(f(i))
  {
  case 4:
    assert(i==3);
    break;
    
  case 5:
    assert(i==4);
    break;

  default:
    assert(0);
  }
}

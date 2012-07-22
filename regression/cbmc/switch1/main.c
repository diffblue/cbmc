int main()
{
  int i;
  
  switch(i)
  {
  case 0:
  case 1:
    assert(i==0 || i==1);
    break;

  case 2:
    assert(i==2);
    break;
    
  default:
    assert(i!=0 && i!=1 && i!=2);
  }
}

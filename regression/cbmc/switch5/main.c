int main()
{
  unsigned int i, j;
  
  switch(i)
  {
  case 10:
    j=10;
    break;
    
  default:;
    j=i+1;
  }

  // this should fail
  assert(j==i+1);
}

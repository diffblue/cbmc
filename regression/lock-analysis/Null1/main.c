int main()
{
  int y;
  int *x;
  
  if(y==1)
    x=&y;
  else
    x=0;
  
  assert(!(x==0));
  
  return 0;
}

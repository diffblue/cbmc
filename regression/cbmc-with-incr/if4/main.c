int main()
{
  int x;

  __CPROVER_assume(x==1);
  
  if(x==2)
    x++;
  
  // this should pass
  assert(x==1);
}

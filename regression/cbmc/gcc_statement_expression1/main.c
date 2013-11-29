int main()
{
  int x;
  int y;

  // as a side-effect  
  ({ x=1; x;});
  
  assert(x==1);
  
  x= ({ y=1; 2; });

  assert(x==2);
  assert(y==1);
  
  // inside an initializer: a needs to be visible
  // before doing the initializer

  int a=({ int b=(long int)&a; b; });
  
  return 0;
}

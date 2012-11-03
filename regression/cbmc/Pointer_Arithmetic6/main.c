int main()
{
  int a[10];
  int x;
  
  a[1]=1000;
  
  x=*(a+1);
  
  assert(x==1000);
}

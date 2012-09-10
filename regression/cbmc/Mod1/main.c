int main()
{
  int x, y;
  
  x=y;  
  x%=10;
  assert(x!=-1); // should fail
}

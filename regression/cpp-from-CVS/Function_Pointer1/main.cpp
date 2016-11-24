int f(int x)
{
  assert(x==1);
}

int main()
{
  int (*p)(int);
  
  p=f;
  
  p(1);
}

int foo(int x)
{
  if(x<10) return foo(x+1);
  return x;
}

int main()
{
  assert(foo(0)==10);
}

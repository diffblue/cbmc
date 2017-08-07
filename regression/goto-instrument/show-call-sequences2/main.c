int foo(int x)
{
  if (x==3)
  {
    return 0;
  }
  else
  {
    return foo(3);
  }
}

int main()
{
  foo(0);
  return 0;
}
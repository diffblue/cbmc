int foo(int *x)
{
  if(*x)
  {
    int y = 9;
  }
  else
  {
    int z = 4;
  }
}

int main()
{
  int x;
  foo(&x);
}

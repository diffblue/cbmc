int foo(int)
{
  return 0;
}

unsigned some_function(void)
{
}

int main()
{
  int i;
  i=(some_function()) - 0; // not unary minus

  return (foo)((1));
}


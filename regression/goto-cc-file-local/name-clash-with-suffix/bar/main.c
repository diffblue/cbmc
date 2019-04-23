static int static_fun()
{
  return 3;
}

int bar()
{
  return static_fun();
}

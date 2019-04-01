static int bar()
{
  assert(0);
  return 1;
}

static int foo()
{
  return bar();
}

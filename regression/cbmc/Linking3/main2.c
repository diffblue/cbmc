// these are supposed to be file-local

static int my_f()
{
  unsigned int local;
  return 2;
}

int m2()
{
  return my_f();
}

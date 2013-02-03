// these are supposed to be file-local

static int my_f()
{
  int local;
  return 1;
}

int m1()
{
  return my_f();
}

int m2();

int main()
{
  assert(m1()==1);
  assert(m2()==2);
}

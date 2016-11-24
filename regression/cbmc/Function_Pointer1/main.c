void foo()
{
  // pointer to self; foo needs to be
  // visible in the initializer
  void *p=foo;
}

int x = 0;

void f1(void)
{
  x = 1;
}

void call(void (*f)())
{
  f();
}

int main()
{
  call(f1);
}

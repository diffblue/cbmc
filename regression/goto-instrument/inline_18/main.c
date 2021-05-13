inline int *foo()
{
  int dummy;
  int *ptr = &dummy;
  return ptr;
}

int main()
{
  int *ptr = foo();
  *ptr = 42;
  return 0;
}

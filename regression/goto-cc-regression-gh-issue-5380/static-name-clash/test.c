static inline int foo()
{
  return 42;
}

int bar();

int test()
{
  return foo() + bar();
}

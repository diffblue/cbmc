int foo(int);

int bar(int i) __CPROVER_requires(i > 0)
  __CPROVER_ensures(__CPROVER_return_value > 0)
{
  return foo(i);
}

int main()
{
  int i;
  bar(i);
}

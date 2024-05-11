[[nodiscard]] int foo(void)
{
  return 1;
}

#ifndef _MSC_VER
[[__nodiscard__]]
#endif
int bar(void)
{
  return 2;
}

int main()
{
  return foo() + bar();
}

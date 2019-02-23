int function_to_call(int a)
{
  int local = 1;
  return a + local;
}

int main()
{
  int a;
  unsigned int b;
  a = 0;
  a = -100;
  a = 2147483647;
  b = a * 2;
  a = -2147483647;
  a = function_to_call(a);
  b = function_to_call(b);

  __CPROVER_assert(0, "");
}

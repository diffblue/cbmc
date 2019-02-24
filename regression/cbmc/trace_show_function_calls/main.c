int function_to_call(int a)
{
  int local = 1;
  return a + local;
}

int function_without_body(int p);

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
  a = function_without_body(123);

  __CPROVER_assert(0, "");
}

int main()
{
  int a;
  unsigned int b;
  float f;

  a = 0;
  a = -100;
  a = 2147483647;
  b = a * 2;
  a = -2147483647;
  f = 0.1f;

  __CPROVER_assert(0, "");
}

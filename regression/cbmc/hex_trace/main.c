int main()
{
  int a;
  unsigned int b;
  float f;
  char *p;

  a = 0;
  a = -100;
  a = 2147483647;
  b = a * 2;
  a = -2147483647;
  f = 0.1f;
  p = (char *)123;

  __CPROVER_assert(0, "");
}

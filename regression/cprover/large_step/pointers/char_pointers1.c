int main()
{
  int x;
  char *p = (char *)&x;
  p[0] = 0;
  p[1] = 0;
  p[2] = 0;
  p[3] = 0;
  __CPROVER_assert(x == 0, "property 1");
}

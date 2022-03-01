int main()
{
  int x = 0x01020304;
  char *p = (char *)&x;

  // passes on little endinan
  __CPROVER_assert(p[0] == 0x04, "property 1");
  __CPROVER_assert(p[1] == 0x03, "property 2");
  __CPROVER_assert(p[2] == 0x02, "property 3");
  __CPROVER_assert(p[3] == 0x01, "property 4");
  return 0;
}

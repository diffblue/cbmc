// N5008 [conv.prom]/1, [over.ics.rank]/4: an integral promotion is to int
// (or unsigned int) only, so it ranks above the conversion to a long of the
// same width (32-bit long on i386 and Windows) and h(us) is not ambiguous
extern "C" void __CPROVER_assert(bool, const char *);
int g(unsigned)
{
  return 2;
}
int g(unsigned long)
{
  return 4;
}
int h(int)
{
  return 1;
}
int h(long)
{
  return 3;
}
int k(double)
{
  return 5;
}
int k(long double)
{
  return 6;
}
int main()
{
  char32_t c = U'x';
  unsigned short us = 1;
  __CPROVER_assert(g(c) == 2, "char32_t promotes to unsigned int");
  __CPROVER_assert(h(us) == 1, "unsigned short promotes to int");
  __CPROVER_assert(k(1.0f) == 5, "float promotes to double");
  __CPROVER_assert(h(us) == 3, "WRONG (must FAIL)");
  return 0;
}

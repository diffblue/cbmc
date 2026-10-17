// N5008 [conv.qual]/3, [basic.fundamental]/1, /11: char, signed char,
// unsigned char and char8_t are distinct types, so a pointer to one does
// not convert to a pointer to another of the same representation (char
// is signed on x86-64 and unsigned on aarch64), and these calls are not
// ambiguous
extern "C" void __CPROVER_assert(bool, const char *);
int f(const char *)
{
  return 1;
}
int f(const signed char *)
{
  return 2;
}
int f(const unsigned char *)
{
  return 3;
}
int f(const char8_t *)
{
  return 4;
}
int main()
{
  char c[2] = "a";
  signed char s[2] = {1, 0};
  unsigned char u[2] = {1, 0};
  __CPROVER_assert(f(c) == 1 && f("a") == 1, "char");
  __CPROVER_assert(f(s) == 2, "signed char");
  __CPROVER_assert(f(u) == 3, "unsigned char");
  __CPROVER_assert(f(u8"a") == 4, "char8_t");
  __CPROVER_assert(f(c) == 2, "WRONG (must FAIL)");
  return 0;
}

// N5008 [conv.prom]/2: a prvalue of type char8_t, char16_t, char32_t or
// wchar_t can be converted to the first of int, unsigned int, long,
// unsigned long, long long, unsigned long long that can represent all the
// values of its underlying type -- for a 32-bit char32_t that is unsigned
// int, even though it is as wide as int.  The front end did not promote a
// char32_t at all, so `f(c)' against the int/unsigned/long/... constructor
// overloads of a big-integer class had no best candidate ("found no match
// for symbol 'f'"; mp_integer in CBMC's own convert_character_literal.cpp,
// dog-fooding).  [over.ics.rank]/4.2 prefers the promotion.
extern "C" void __CPROVER_assert(bool, const char *);
struct big
{
  long long v;
  big(int x) : v(x)
  {
  }
  big(unsigned x) : v(x)
  {
  }
  big(long x) : v(x)
  {
  }
  big(unsigned long x) : v(x)
  {
  }
  big(long long x) : v(x)
  {
  }
  big(unsigned long long x) : v(x)
  {
  }
};
long long f(const big &b)
{
  return b.v;
}
int g(int)
{
  return 1;
}
int g(unsigned)
{
  return 2;
}
int g(long)
{
  return 3;
}
int main()
{
  char32_t c = U'x';
  char16_t d = u'y';
  wchar_t w = L'z';
  __CPROVER_assert(f(c) == 'x', "char32_t through a converting constructor");
  __CPROVER_assert(f(d) == 'y' && f(w) == 'z', "char16_t and wchar_t");
  __CPROVER_assert(g(c) == 2, "char32_t promotes to unsigned int");
  __CPROVER_assert(g(d) == 1 && g(w) == 1, "char16_t, wchar_t promote to int");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

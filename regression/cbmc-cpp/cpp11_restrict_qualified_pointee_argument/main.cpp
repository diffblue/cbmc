extern "C" void __CPROVER_assert(bool, const char *);
// glibc declares strtod etc. with a restrict-qualified pointee:
//   double strtod(const char *__restrict, char **__restrict);
//   size_t mbsrtowcs(wchar_t *, const char **__restrict, size_t, mbstate_t *);
long parse(const char *__restrict s, char **__restrict end)
{
  long v = 0;
  while(*s >= '0' && *s <= '9')
    v = v * 10 + (*s++ - '0');
  if(end)
    *end = const_cast<char *>(s);
  return v;
}
unsigned count(const char **__restrict src, unsigned n)
{
  unsigned c = 0;
  for(unsigned i = 0; i < n && (*src)[i]; ++i)
    ++c;
  return c;
}
template <class T>
T do_parse(const char *a, char **p2)
{
  return static_cast<T>(parse(a, p2));
}
int main()
{
  const char *text = "42x";
  char *end = nullptr;
  int v = do_parse<int>(text, &end);
  __CPROVER_assert(
    v == 42 && end == text + 2,
    "char ** argument binds to a char *restrict * parameter");
  const char *src = "abc";
  __CPROVER_assert(
    count(&src, 10) == 3, "const char ** to const char **restrict");
  __CPROVER_assert(v == 43, "WRONG (must FAIL)");
}

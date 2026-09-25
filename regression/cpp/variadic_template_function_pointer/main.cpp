// Test template argument deduction through function pointer types
// with variadic template parameter packs.
namespace N
{
template <typename T, typename R = T, typename C, typename... Base>
R func(
  T (*convf)(const C *, C **, Base...),
  const char *name,
  const C *str,
  Base... base)
{
  R ret;
  C *endptr;
  T tmp = convf(str, &endptr, base...);
  ret = tmp;
  return ret;
}
} // namespace N

long my_strtol(const char *s, char **e, int base)
{
  return 0;
}
float my_strtof(const char *s, char **e)
{
  return 0.0f;
}

int main()
{
  // With explicit template args
  int x = N::func<long, int>(&my_strtol, "test", "123", 10);
  // With all args deduced (R defaults to T=long)
  long y = N::func(&my_strtol, "test", "123", 10);
  // With empty variadic pack (Base... = empty)
  float z = N::func(&my_strtof, "stof", "3.14");
  return x + y + (int)z;
}

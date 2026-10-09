// C++11 user-defined string literal
constexpr unsigned long operator""_len(const char *s, unsigned long n)
{
  return n;
}
int main()
{
  auto r = "hello"_len;
  __CPROVER_assert(r == 5, "string udl length");
  return 0;
}

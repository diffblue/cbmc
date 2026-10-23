// C++11 raw string literals
int main()
{
  const char *s = R"(hello "world")";
  __CPROVER_assert(s[0] == 'h', "raw string");
  __CPROVER_assert(s[6] == '"', "raw string quote");
  return 0;
}

// C++11 user-defined literal
constexpr long long operator""_kb(unsigned long long v)
{
  return v * 1024;
}
int main()
{
  long long r = 4_kb;
  __CPROVER_assert(r == 4096, "user defined literal");
  return 0;
}

// C++11 user-defined literals
constexpr long long operator""_km(unsigned long long v)
{
  return v * 1000;
}
int main()
{
  long long d = 5_km;
  __CPROVER_assert(d == 5000, "user-defined literal");
  return 0;
}

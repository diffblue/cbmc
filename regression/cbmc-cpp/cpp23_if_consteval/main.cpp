// C++23 if consteval
// CBMC performs runtime verification, so if consteval always takes the
// runtime (else) branch.
constexpr int compute(int x)
{
  if consteval
  {
    return x * 2;
  }
  else
  {
    return x * 3;
  }
}

constexpr int no_else(int x)
{
  if consteval
  {
    return x * 2;
  }
  return x * 3;
}

int main()
{
  int r = compute(7);
  __CPROVER_assert(r == 21, "if consteval takes runtime branch");
  int s = no_else(5);
  __CPROVER_assert(s == 15, "if consteval without else");
  return 0;
}

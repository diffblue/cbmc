// C++23 if consteval
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

int main()
{
  constexpr int r = compute(7);
  __CPROVER_assert(r == 14, "if consteval");
  return 0;
}

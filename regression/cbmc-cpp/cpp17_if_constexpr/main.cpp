// C++17 if constexpr
template <typename T>
int process(T val)
{
  if constexpr(sizeof(T) == 1)
    return val + 100;
  else
    return val;
}
int main()
{
  int r = process(42);
  __CPROVER_assert(r == 42, "if constexpr discard");
  return 0;
}

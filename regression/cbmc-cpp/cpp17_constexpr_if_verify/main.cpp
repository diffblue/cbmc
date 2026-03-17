// C++17 constexpr if
template <typename T>
int process(T v)
{
  if constexpr(sizeof(T) > 4)
    return 1;
  else
    return 0;
}
int main()
{
  int r1 = process(42);
  int r2 = process(42LL);
  __CPROVER_assert(r1 == 0, "int is small");
  __CPROVER_assert(r2 == 1, "long long is big");
  return 0;
}

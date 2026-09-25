// C++11 variadic template with mixed types in pack
template <typename T>
T identity(T x)
{
  return x;
}

template <typename T, typename... Rest>
T first_of(T first, Rest... rest)
{
  return first;
}

int main()
{
  int r = first_of(42, 3.14, true);
  __CPROVER_assert(r == 42, "first_of mixed types");
  return 0;
}

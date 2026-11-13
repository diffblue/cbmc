int sum(int x)
{
  return x;
}

template <typename T, typename... Rest>
int sum(T first, Rest... rest)
{
  return first + sum(rest...);
}

int main()
{
  int r = sum(1, 2, 3);
  __CPROVER_assert(r == 6, "sum(1,2,3) == 6");
  return 0;
}

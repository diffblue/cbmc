// C++20 trailing requires clause
template <typename T>
T add(T a, T b) requires(__is_integral(T))
{
  return a + b;
}

int main()
{
  int r = add(1, 2);
  __CPROVER_assert(r == 3, "trailing requires");
  return 0;
}

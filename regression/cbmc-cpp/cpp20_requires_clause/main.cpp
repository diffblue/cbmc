// C++20 requires clause
template <typename T>
requires(__is_same(T, int)) T add(T a, T b)
{
  return a + b;
}

int main()
{
  int r = add(1, 2);
  __CPROVER_assert(r == 3, "requires clause");
  return 0;
}

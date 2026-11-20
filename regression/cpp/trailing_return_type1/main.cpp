// C++11 trailing return types with abstract declarators
struct S
{
  int x;
  auto get() -> int &
  {
    return x;
  }
  auto get_c() const -> const int &
  {
    return x;
  }
  auto get_p() -> int *
  {
    return &x;
  }
};

auto add(int a, int b) -> int
{
  return a + b;
}

int main()
{
  S s;
  s.x = 42;
  int &r = s.get();
  return add(r, 0);
}

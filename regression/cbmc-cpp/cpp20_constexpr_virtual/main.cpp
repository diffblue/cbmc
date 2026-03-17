// C++20 constexpr virtual functions
struct Base
{
  constexpr virtual int value() const
  {
    return 1;
  }
  virtual ~Base() = default;
};
struct Derived : Base
{
  constexpr int value() const override
  {
    return 2;
  }
};
int main()
{
  Derived d;
  Base &b = d;
  int v = b.value();
  __CPROVER_assert(v == 2, "virtual dispatch");
  return 0;
}

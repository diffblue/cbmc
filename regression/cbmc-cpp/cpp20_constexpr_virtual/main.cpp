// C++20 constexpr virtual functions
struct Base
{
  constexpr virtual int f() const
  {
    return 1;
  }
};
struct Derived : Base
{
  constexpr int f() const override
  {
    return 2;
  }
};

int main()
{
  Derived d;
  const Base &b = d;
  __CPROVER_assert(b.f() == 2, "virtual dispatch");
}

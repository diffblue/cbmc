// C++11 final and override
struct Base
{
  virtual int f()
  {
    return 1;
  }
  virtual int g() final
  {
    return 2;
  }
};
struct Derived final : Base
{
  int f() override
  {
    return 3;
  }
};
int main()
{
  Derived d;
  Base &b = d;
  __CPROVER_assert(b.f() == 3, "override");
  __CPROVER_assert(b.g() == 2, "final");
  return 0;
}

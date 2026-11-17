// C++11 inheriting constructors
struct Base
{
  int x;
  Base(int v) : x(v)
  {
  }
};
struct Derived : Base
{
  using Base::Base;
};
int main()
{
  Derived d(42);
  __CPROVER_assert(d.x == 42, "inheriting ctor");
  return 0;
}

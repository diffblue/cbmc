// Test that using declarations inside class bodies bring base class
// members into the derived class scope alongside local overloads.
struct Base
{
  static void foo(int *p)
  {
  }
};

struct Derived : Base
{
  using Base::foo;
  static void foo(int x)
  {
  }
};

int main()
{
  int x;
  Derived::foo(&x);
  Derived::foo(42);
}

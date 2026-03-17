// Test that delegating constructors do not generate default base class
// initialization, which would fail for base classes without default
// constructors.
struct Base
{
  Base(int x) : val(x)
  {
  }
  virtual ~Base()
  {
  }
  int val;
};

struct Derived : Base
{
  Derived(int x) : Base(x)
  {
  }
  Derived(int x, int y) : Derived(x + y)
  {
  }
};

// Also test delegating constructors in template classes.
template <typename T>
struct S
{
  S() : S(0)
  {
  }
  S(T x) : val(x)
  {
  }
  T val;
};

int main()
{
  Derived d(1, 2);
  __CPROVER_assert(d.val == 3, "delegating constructor");
  S<int> s;
  __CPROVER_assert(s.val == 0, "template delegating constructor");
  return 0;
}

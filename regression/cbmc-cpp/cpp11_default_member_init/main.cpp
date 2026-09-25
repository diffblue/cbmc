// C++11 default member initializers (NSDMI)
struct A
{
  int x = 10;
  int y = 20;
};

struct B
{
  int x = 10;
  int y;
  int z = 30;
};

struct C
{
  int x = 10;
  int y = 20;
  C()
  {
  }
};

struct D
{
  int x = 10;
  int y = 20;
  D(int v) : x(v)
  {
  }
};

int main()
{
  // POD default construction applies defaults
  A a;
  __CPROVER_assert(a.x == 10, "A::x default");
  __CPROVER_assert(a.y == 20, "A::y default");

  // Mixed default/non-default
  B b;
  __CPROVER_assert(b.x == 10, "B::x default");
  __CPROVER_assert(b.z == 30, "B::z default");

  // Aggregate init overrides defaults
  A a2{5, 6};
  __CPROVER_assert(a2.x == 5, "A::x overridden");
  __CPROVER_assert(a2.y == 6, "A::y overridden");

  // User-declared empty ctor applies defaults
  C c;
  __CPROVER_assert(c.x == 10, "C::x default with ctor");
  __CPROVER_assert(c.y == 20, "C::y default with ctor");

  // Explicit member init overrides default, others use default
  D d(42);
  __CPROVER_assert(d.x == 42, "D::x explicit");
  __CPROVER_assert(d.y == 20, "D::y default");

  return 0;
}

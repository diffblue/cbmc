// N5008 [namespace.udecl]/2, [class.inhctor.init] (C++17 inheriting
// constructors, P0136): a using-declaration naming a base-class constructor
// inherits the base's constructors, including its default constructor.
// Initialization of a derived object by an inherited default constructor
// proceeds exactly as a defaulted default constructor of the derived class.
// In particular a derived class that declares only defaulted move members
// (which suppress the implicit default constructor, [class.default.ctor]/1)
// remains default-constructible through the inherited default constructor --
// the shape of libstdc++'s __uniq_ptr_data.  Cross-checked against g++ and
// clang++.

extern "C" void __CPROVER_assert(int, const char *);

struct B
{
  int x;
  B() : x(7)
  {
  }
  B(int v) : x(v)
  {
  }
};

// plain inheriting constructor
struct D : B
{
  using B::B;
};

// inheriting constructor + user-declared (defaulted) move constructor: the
// implicit default constructor is suppressed, the inherited one is used
struct E : B
{
  using B::B;
  E(E &&) = default;
};

// the class's own default constructor takes precedence over the inherited one
struct F : B
{
  using B::B;
  F() : B(9)
  {
  }
};

int main()
{
  D d;
  __CPROVER_assert(d.x == 7, "inherited default constructor runs");
  D d2(3);
  __CPROVER_assert(d2.x == 3, "inherited int constructor runs");
  E e;
  __CPROVER_assert(
    e.x == 7, "inherited default constructor with defaulted move members");
  F f;
  __CPROVER_assert(f.x == 9, "own default constructor takes precedence");
  return 0;
}

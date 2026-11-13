// A struct constant (struct_exprt) has one operand per non-static data
// member; a C++ class type's component list additionally holds member
// functions, member types and static data members.  Indexing a struct
// constant with struct_union_typet::component_number (the position among
// ALL components) picked the wrong operand -- or ran off the end -- as soon
// as a member function was declared BEFORE a data member: `constexpr S s;
// static_assert(s.a == 3)' could not be evaluated for `struct S { int f();
// int a = 3; }'.  data_component_number counts the storage components only;
// the simplifier, struct_exprt::component and the constant evaluator use it.
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  int f() const
  {
    return 1;
  }
  using type = int;
  static const int k = 9;
  int a = 3;
  constexpr int g() const
  {
    return a;
  }
  int b = 4;
  constexpr int h() const
  {
    return b;
  }
};
constexpr S s;
static_assert(s.a == 3, "member after a method");
static_assert(s.b == 4, "second member");
static_assert(s.g() == 3 && s.h() == 4, "member functions reading them");

struct P
{
  constexpr P(int x) : v(x)
  {
  }
  constexpr int twice() const
  {
    return 2 * v;
  }
  int v;
};
constexpr P p(21);
static_assert(p.v == 21 && p.twice() == 42, "constructor before member");

int main()
{
  __CPROVER_assert(s.a + s.b == 7 && p.v == 21, "run time");
  __CPROVER_assert(s.b == 3, "WRONG (must FAIL)");
}

extern "C" void __CPROVER_assert(bool, const char *);
#include <string>
// N5008 [dcl.init.ref]/5.3: an rvalue reference (like a const lvalue
// reference) to a class type can be initialised from an expression of an
// unrelated type: a temporary of the referenced type is copy-initialised
// (converting constructor) and the reference binds to it.  /5.4's "shall
// not be an lvalue" only applies to reference-RELATED types.
struct W
{
  int v;
  W(const char *) : v(1)
  {
  }
  W(int x) : v(x)
  {
  }
};
struct Base
{
  int b;
  Base(int x) : b(x)
  {
  }
};
struct Derived : Base
{
  Derived(int x) : Base(x)
  {
  }
};
int w(W &&s)
{
  return s.v;
}
int w(const W &s)
{
  return -s.v;
} // lvalue W: this one
int w2(W &&s, int)
{
  return s.v;
}
int g(std::string &&s)
{
  return s.size();
}
int b(Base &&x)
{
  return x.b;
}
int b(const Base &x)
{
  return -x.b;
}
struct X1
{
  std::string n;
  X1(std::string &&s, int) : n(std::move(s))
  {
  }
};
int main()
{
  __CPROVER_assert(w(5) == 5, "W&& from int prvalue: converting constructor");
  __CPROVER_assert(
    w("ab") == 1, "W&& from a string literal (an lvalue of unrelated type)");
  const char *p = "x";
  __CPROVER_assert(w(p) == 1, "W&& from a const char* lvalue");
  W lv(7);
  __CPROVER_assert(
    w(lv) == -7, "an lvalue W binds the const W& overload, not W&&");
  __CPROVER_assert(
    w2("ab", 0) == 1, "W&& from literal with a second parameter");
  __CPROVER_assert(g("loop") == 4, "std::string&& from a string literal");
  Derived d(3);
  __CPROVER_assert(
    b(d) == -3,
    "reference-related lvalue: Base&& not viable, const Base& taken");
  __CPROVER_assert(
    b(Derived(4)) == 4, "reference-related prvalue binds Base&&");
  X1 x1("loop", 1);
  __CPROVER_assert(
    x1.n == "loop", "constructor with std::string&& parameter from a literal");
  return 0;
}

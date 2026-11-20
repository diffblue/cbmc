// N5008 [class.mem.general]/9.4: the noexcept-specifier of a member
// function is a complete-class context: it can name later data members,
// static members and, through `this' ([expr.prim.this]/4), later member
// functions; [except.spec]/2.
extern "C" void __CPROVER_assert(bool, const char *);
struct Throwing
{
  void f()
  {
  }
};
struct Quiet
{
  void f() noexcept
  {
  }
};
struct S
{
  void e() noexcept(noexcept(m.f()))
  {
  }
  void q() noexcept(noexcept(n.f()))
  {
  }
  static void s1() noexcept(noexcept(s2()))
  {
  }
  static void s2()
  {
  }
  void k() const noexcept(noexcept(l()))
  {
  }
  void l() const
  {
  }
  Throwing m;
  Quiet n;
};
int main()
{
  S s;
  __CPROVER_assert(!noexcept(s.e()), "later data member, throwing");
  __CPROVER_assert(noexcept(s.q()), "later data member, non-throwing");
  __CPROVER_assert(!noexcept(S::s1()), "static member");
  __CPROVER_assert(!noexcept(s.k()), "const member");
  __CPROVER_assert(noexcept(s.e()), "WRONG (must FAIL)");
}

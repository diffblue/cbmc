extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [over.match.oper]/1, [over.ass]: `a = b' with a class operand is
// resolved among the class's assignment operators, templates included.
// [class.copy.assign]/1: a template is never a copy assignment operator,
// so the implicitly declared one remains, a non-template that wins for an
// argument of the class type itself ([over.match.best]/2.4)
struct pod
{
  int which;
  template <class F>
  pod &operator=(const F &)
  {
    which = 4;
    return *this;
  }
};
// a class with only an assignment operator template, as libc++'s
// std::function has besides its copy and move assignment
struct fn
{
  int which = 0;
  template <class F>
  fn &operator=(F &&)
  {
    which = 5;
    return *this;
  }
};
int main()
{
  fn g;
  g = [] { return 1; };
  __CPROVER_assert(g.which == 5, "assignment from a lambda");
  pod a{1}, b{2};
  const pod &cb = b;
  a = cb;
  __CPROVER_assert(a.which == 2, "implicit copy assignment");
  a = 1.0;
  __CPROVER_assert(a.which == 4, "assignment operator template");
  pod c{3};
  c = static_cast<pod &&>(b);
  __CPROVER_assert(c.which == 2, "implicit move assignment");
  __CPROVER_assert(a.which == 2, "WRONG (must FAIL)");
  return 0;
}

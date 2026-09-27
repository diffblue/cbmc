extern "C" void __CPROVER_assert(bool, const char *);
// a non-trivially-copyable class: its by-value return is lowered to
// construction in the caller's storage through a hidden result parameter
struct value
{
  int v;
  value() : v(-1)
  {
  }
  ~value()
  {
  }
};
// a variadic function ([dcl.fct]/6): the arguments beyond `first' are not
// bound to declared parameters
value make(int first, ...)
{
  value r;
  r.v = first;
  return r;
}
// the libc++ ranges shape: `_Fn...' with a non-pack _Fn is `_Fn, ...'
template <class F>
value forward_first(F first...)
{
  value r;
  r.v = first;
  return r;
}
int main()
{
  value a = make(7, 3, 4);
  __CPROVER_assert(a.v == 7, "returned through a variadic call");
  value b = forward_first(5, 9);
  __CPROVER_assert(b.v == 5, "returned through a variadic template call");
  value c = make(1);
  __CPROVER_assert(c.v == 1, "no variadic arguments");
  __CPROVER_assert(a.v == 3, "WRONG (must FAIL)");
}

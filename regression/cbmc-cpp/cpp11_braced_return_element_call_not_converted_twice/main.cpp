// N5008 [stmt.return]/2, [dcl.init.list]/3.7: `return {link(m,
// std::move(lib)), true};' into a class with a constructor template
// (std::pair) copy-list-initializes the result by that constructor, the
// clauses its arguments.  The clause `link(m, std::move(lib))' is
// type-checked once (its `model &&' parameter binds the xvalue).  The
// front end handed the type-checked clause to the constructor resolution
// unmarked, which type-checked the call again and bound the converted
// argument as an lvalue: "invalid implicit conversion from 'struct model
// &' to 'struct model &&'" (CBMC's own link_to_library.cpp, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
T &&move(T &x)
{
  return static_cast<T &&>(x);
}
struct model
{
  int n = 0;
  model() = default;
  model(model &&o) : n(o.n)
  {
    o.n = -1;
  }
  model(const model &) = delete;
};
int link(model &dest, model &&src)
{
  dest.n += src.n;
  return dest.n;
}
template <class A, class B>
struct pr
{
  A first;
  B second;
  template <class U, class V>
  pr(U &&u, V &&v) : first(u), second(v)
  {
  }
};
pr<int, bool> add(model &m)
{
  model lib;
  lib.n = 4;
  return {link(m, move(lib)), true};
}
int main()
{
  model m;
  m.n = 1;
  pr<int, bool> r = add(m);
  __CPROVER_assert(
    r.first == 5 && r.second, "braced return with a call taking an xvalue");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

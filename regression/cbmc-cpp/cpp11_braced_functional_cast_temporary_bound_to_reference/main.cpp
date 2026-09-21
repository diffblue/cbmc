extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [class.temporary]/2, [conv.rval], [dcl.init.ref]/5.3: a prvalue of
// class type bound to a reference parameter is materialised ONCE and the
// reference denotes that object; no further copy takes place.  `T{args}`
// (a braced functional cast) was materialised and then copied BITWISE into a
// second temporary that the reference was bound to, so a member pointing at
// the object itself (self, or std::function's manager/functor pointers, or a
// std::string's local buffer pointer) pointed into the first, already dead,
// temporary.  `T(args)` never had the extra copy.
struct Tracker
{
  int v;
  int *self;
  Tracker(int x) : v(x), self(&v)
  {
  }
  Tracker(const Tracker &o) : v(o.v), self(&v)
  {
    __CPROVER_assert(o.self == &o.v, "the copy source is the live object");
  }
  ~Tracker()
  {
    self = nullptr;
  }
};
struct Inner
{
  int a;
  Tracker t;
  Inner(int a_, const Tracker &t_) : a(a_), t(t_)
  {
  }
  Inner(const Inner &o) : a(o.a), t(o.t)
  {
  }
};
struct Outer
{
  int x;
  Inner in;
  Outer(int x_, const Inner &in_) : x(x_), in(in_)
  {
  }
};
int take(const Inner &in)
{
  return in.a + in.t.v;
}
int take_rv(Inner &&in)
{
  return in.a + in.t.v;
}
int main()
{
  __CPROVER_assert(take({1, 2}) == 3, "A: braced list to const T&");
  __CPROVER_assert(take(Inner{5, 6}) == 11, "B: T{} temporary to const T&");
  __CPROVER_assert(take(Inner(5, 6)) == 11, "C: T() temporary to const T&");
  __CPROVER_assert(take_rv(Inner{7, 8}) == 15, "D: T{} temporary to T&&");
  Outer o{10, {1, 2}};
  __CPROVER_assert(o.in.a == 1 && o.in.t.v == 2, "E: nested braces");
  Outer r(10, Inner{5, 6});
  __CPROVER_assert(
    r.in.a == 5 && r.in.t.v == 6, "F: parens ctor, T{} argument");
  Outer u{10, Inner{5, 6}};
  __CPROVER_assert(
    u.in.a == 5 && u.in.t.v == 6, "G: braces ctor, T{} argument");
  Outer t{10, Inner(5, 6)};
  __CPROVER_assert(
    t.in.a == 5 && t.in.t.v == 6, "H: braces ctor, T() argument");
  return 0;
}

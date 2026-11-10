// N5008 [dcl.contract.res]/1, [expr.call]/9, [class.copy.elision]: the
// result name of a postcondition denotes the result object.  Checking the
// postconditions of a function returning a class must not copy or move
// the result (guaranteed elision of `return T{x};', a non-copyable type);
// for a function returning a reference the result name refers to the
// object the reference is bound to.  The postconditions are evaluated
// after the local variables are destroyed ([stmt.return]/5), and not when
// the function exits by an exception.
extern "C" void __CPROVER_assert(bool, const char *);
int ctors = 0, copies = 0, moves = 0, dtors = 0;
struct T
{
  int v;
  T *self;
  T(int x) : v(x), self(this)
  {
    ++ctors;
  }
  T(const T &o) : v(o.v), self(this)
  {
    ++copies;
  }
  T(T &&o) : v(o.v), self(this)
  {
    ++moves;
  }
  ~T()
  {
    ++dtors;
  }
};
struct U // not copyable, not movable
{
  int v;
  U(int x) : v(x)
  {
  }
  U(const U &) = delete;
  U(U &&) = delete;
};
T make(const int x) post(r : r.v == x)
{
  return T{x};
}
T named(const int x) post(r : r.v == x + 1)
{
  T t{x + 1};
  return t;
}
U fixed(const int x) post(r : r.v == x)
{
  return U{x};
}
int g = 7;
int destroyed = 0;
struct L
{
  ~L()
  {
    ++destroyed;
  }
};
int after_locals(const int x) post(r : destroyed == 1 && r == x)
{
  L l;
  return x;
}
int thrower(const int x) post(r : r > 0)
{
  if(x < 0)
    throw 1;
  return x + 1;
}
int &ref() post(r : &r == &g && r == 7)
{
  return g;
}
const int &cref(const int &a) post(r : &r == &a)
{
  return a;
}
int &&rref() post(r : r == 7)
{
  return static_cast<int &&>(g);
}
int main()
{
  {
    T a = make(3);
    __CPROVER_assert(
      a.v == 3 && ctors == 1 && copies == 0 && moves == 0,
      "prvalue: one construction");
    __CPROVER_assert(a.self == &a, "prvalue: object identity");
  }
  __CPROVER_assert(dtors == 1, "prvalue: one destruction");
  ctors = copies = moves = dtors = 0;
  {
    T b = named(4);
    __CPROVER_assert(
      b.v == 5 && ctors == 1 && copies == 0 && moves <= 1,
      "named: no extra copy");
  }
  __CPROVER_assert(dtors == ctors + moves, "named: balanced destructors");
  U u = fixed(9);
  __CPROVER_assert(u.v == 9, "non-copyable");
  ref() = 8;
  __CPROVER_assert(g == 8, "write through returned reference");
  g = 7;
  int y = 1;
  __CPROVER_assert(&cref(y) == &y, "const reference binds");
  __CPROVER_assert(rref() == 7, "rvalue reference");
  __CPROVER_assert(after_locals(5) == 5, "after the locals");
  bool caught = false;
  try
  {
    thrower(-1);
  }
  catch(int)
  {
    caught = true;
  }
  __CPROVER_assert(caught, "exceptional exit");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

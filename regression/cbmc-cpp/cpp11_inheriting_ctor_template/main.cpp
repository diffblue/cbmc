// N5008 [namespace.udecl]/2, [class.inhctor.init]: a using-declaration naming
// a base-class constructor inherits the base's constructors *including its
// constructor templates*; initializing a derived object by an inherited
// constructor initializes the base subobject with that constructor and
// default-initializes everything else.  Also [dcl.init.aggr]/1 (C++17): a
// class with inherited constructors is not an aggregate, so construction must
// not fall back to aggregate initialization (dropping arguments).  The
// derived class's own constructor takes precedence over an inherited one of
// the same signature.  Cross-checked against g++ and clang++.

extern "C" void __CPROVER_assert(int, const char *);

struct tag_t
{
};

struct B
{
  int x;
  bool s;
  B() : x(0), s(false)
  {
  }
  template <class... A>
  B(tag_t, A... a) : x(a...), s(true)
  {
  }
};

struct D : B
{
  using B::B;
};

template <class T>
struct BT
{
  T v;
  bool s;
  BT() : v(0), s(false)
  {
  }
  template <class... A>
  BT(tag_t, A... a) : v(a...), s(true)
  {
  }
};

template <class T>
struct DT : BT<T>
{
  using BT<T>::BT;
};

struct E : B
{
  using B::B;
  E(tag_t, int v) : B(), own(v)
  {
  }
  int own = 0;
};

int main()
{
  D d(tag_t{}, 5);
  __CPROVER_assert(d.x == 5 && d.s, "inherited constructor template forwards");
  DT<int> t(tag_t{}, 7);
  __CPROVER_assert(
    t.v == 7 && t.s, "inherited constructor template in a class template");
  E e(tag_t{}, 9);
  __CPROVER_assert(
    e.own == 9 && !e.s, "own constructor takes precedence over inherited");
  return 0;
}

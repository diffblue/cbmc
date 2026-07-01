// N5008 [over.match.oper]/3, [over.match.best]/2: for `a @ b`, member and
// non-member operator candidates form one overload set.  A member operator that
// is a function TEMPLATE is a member candidate too, and its implicit object
// parameter is an exact match for the object argument.  A non-member candidate
// is preferred over a function-template specialization only when their
// conversion sequences are otherwise indistinguishable.
//
// This is the shape of util/message.h's mstreamt (the goto-cc failure on
// ui_message.cpp / parser.cpp / typecheck.cpp): a class derived from a base has
// a member `template <class T> Derived &operator<<(const T&)`, competing with a
// free `operator<<(Base&, ...)`.
//
// f1: `d << 5` -- the free base operator needs a derived-to-base conversion for
//   the object, while the member template's object parameter is an exact
//   `Derived&`, so the member template wins (result convertible to Derived&).
// f2: `d << Tag{}` -- a free NON-template operator whose object parameter is an
//   exact `Derived&` competes with the member template; with equal object
//   conversions the non-template free operator wins ([over.match.best]/2).
// g++/clang++ agree (a.tag==2, b.tag==3).  assertion.3 must FAIL.

struct Base
{
  int tag;
};
inline Base &operator<<(Base &b, int)
{
  b.tag = 1;
  return b;
}

struct Tag
{
};

struct Derived : Base
{
  template <class T>
  Derived &operator<<(const T &)
  {
    tag = 2;
    return *this;
  }
};

inline Derived &operator<<(Derived &d, Tag)
{
  d.tag = 3;
  return d;
}

extern "C" void __CPROVER_assert(int, const char *);

Derived &f1(Derived &d)
{
  return d << 5;
}
Derived &f2(Derived &d)
{
  return d << Tag{};
}

int main()
{
  Derived a;
  a.tag = 0;
  f1(a);
  Derived b;
  b.tag = 0;
  f2(b);
  __CPROVER_assert(
    a.tag == 2, "member template wins when free operator needs derived-to-base");
  __CPROVER_assert(b.tag == 3, "free non-template wins on exact object match");
  __CPROVER_assert(a.tag == 3, "WRONG must FAIL");
  return 0;
}

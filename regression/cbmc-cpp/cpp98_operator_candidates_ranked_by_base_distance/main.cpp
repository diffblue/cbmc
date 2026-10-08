// N5008 [over.ics.rank]/4.4.4: binding an expression of type C to a
// reference to B is better than binding it to a reference to A when B is
// derived from A and C from B.  For `d << 1' the member A::operator<<(int)
// binds d to A&, the non-member operator<<(B &, int) binds it to B&; the
// second argument is an exact match for both, so the non-member is better
// ([over.match.best]/2.1, [over.match.oper]/3).
extern "C" void __CPROVER_assert(bool, const char *);

struct A
{
  int last;
  A() : last(0)
  {
  }
  A &operator<<(int)
  {
    last = 1;
    return *this;
  }
};

struct B : A
{
};

struct D : B
{
};

B &operator<<(B &b, int)
{
  b.last = 2;
  return b;
}

int main()
{
  D d;
  d << 1;
  __CPROVER_assert(d.last == 2, "nearer base wins");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

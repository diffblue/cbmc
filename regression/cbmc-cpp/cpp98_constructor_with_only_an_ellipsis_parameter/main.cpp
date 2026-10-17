// N5008 [dcl.fct]/4, [over.ics.ellipsis]: a constructor `S(...)' accepts
// any argument; the argument of `S c(1)' is not the object argument
// (the front end took a call with as many arguments as parameters to be
// set up with the object argument already in place).
extern "C" void __CPROVER_assert(bool, const char *);

struct T
{
};

struct S
{
  int n;
  S(int) : n(1)
  {
  }
  S(...) : n(2)
  {
  }
};

struct E
{
  int n;
  E(...) : n(3)
  {
  }
};

int main()
{
  T t;
  S b(t);
  S c((T()));
  S d(1);
  S e(&t);
  E x(1);
  E y(&t);
  __CPROVER_assert(
    b.n == 2 && c.n == 2 && d.n == 1 && e.n == 2, "S: ellipsis constructor");
  __CPROVER_assert(x.n == 3 && y.n == 3, "E: only an ellipsis");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

// N5008 [over.best.ics]/7: initializing a parameter of class type ex from an
// argument of the derived class if_ex is a derived-to-base Conversion, a
// standard conversion sequence, which [over.ics.rank]/2.1 ranks better than
// any user-defined conversion sequence.  The front end ranked it as a
// user-defined conversion, so `g(r)' tied g(ex) with g(other) (other has a
// converting constructor from if_ex), and `return r;' into res<> tied
// res(ex) with the copy constructor of res: "does not uniquely resolve"
// (CBMC's own simplify_exprt::resultt<>, eight simplify_expr*.cpp files,
// dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct ex
{
  int id = 0;
};
struct if_ex : ex
{
  if_ex()
  {
    id = 7;
  }
};
struct other
{
  other(if_ex)
  {
  }
};
int g(ex)
{
  return 1;
}
int g(other)
{
  return 2;
}
template <typename T = ex>
struct res
{
  bool changed;
  T e;
  res(T x) : changed(true), e(x)
  {
  }
};
res<> build()
{
  if_ex r;
  return r;
}
int main()
{
  if_ex r;
  __CPROVER_assert(g(r) == 1, "derived-to-base beats user-defined");
  res<> x = build();
  __CPROVER_assert(x.changed && x.e.id == 7, "converting constructor");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

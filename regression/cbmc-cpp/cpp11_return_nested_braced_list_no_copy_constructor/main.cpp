extern "C" void __CPROVER_assert(bool, const char *);
struct chk
{
  bool when;
  int e;
};
struct in_place
{
};
// N5008 [over.best.ics]/4.5: in `return {{b, e}};' the list's only element
// is itself a braced-init-list; for the first parameter of a constructor of
// opt of type opt && or const opt & (the move and copy constructors), no
// user-defined conversion is considered, so only opt(chk) is viable
struct opt
{
  chk value;
  int which;
  opt(opt &&o) : value(o.value), which(1)
  {
  }
  opt(const opt &o) : value(o.value), which(1)
  {
  }
  template <class... A>
  explicit opt(in_place, A &&...a) : value{a...}, which(3)
  {
  }
  opt(chk c) : value(c), which(2)
  {
  }
};
opt get(bool b, int e)
{
  return {{b, e}};
}
int main()
{
  opt o = get(true, 4);
  __CPROVER_assert(o.value.when && o.value.e == 4, "value");
  __CPROVER_assert(o.value.e == 5, "WRONG (must FAIL)");
  return 0;
}

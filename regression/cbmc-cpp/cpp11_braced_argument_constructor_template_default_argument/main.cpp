extern "C" void __CPROVER_assert(bool, const char *);
struct chk
{
  bool when;
  int e;
};
// N5008 [dcl.init.aggr]/1.1: a class with a constructor template is not an
// aggregate, so `{b, e}' converts to `holder' only through a constructor
// taking two arguments ([over.ics.list]/7, [over.match.list]/1.2): the
// copy and move constructors are not viable for it.  The constructor
// template takes the list, U being its default chk ([temp.deduct.call]/1).
struct holder
{
  chk value;
  int which;
  template <class U = chk>
  holder(U u) : value(u), which(2)
  {
  }
};
holder make(bool b, int e)
{
  return {{b, e}};
}
int main()
{
  holder h({true, 4});
  holder r = make(true, 5);
  __CPROVER_assert(h.which == 2 && h.value.when && h.value.e == 4, "direct");
  __CPROVER_assert(r.value.when && r.value.e == 5, "return");
  __CPROVER_assert(h.value.e == 5, "WRONG (must FAIL)");
  return 0;
}

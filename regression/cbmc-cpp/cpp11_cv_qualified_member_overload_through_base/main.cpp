extern "C" void __CPROVER_assert(bool, const char *);
struct base
{
  unsigned v;
  unsigned load(int) const
  {
    return v;
  }
  unsigned load(int) const volatile
  {
    return v + 100;
  }
};
struct derived : base
{
};
int main()
{
  derived d;
  d.v = 3;
  // [over.ics.rank]/3.2.6: binding the implicit object parameter to
  // `const base &' is better than to `const volatile base &'
  __CPROVER_assert(d.load(0) == 3, "the const overload, through a base class");
  base b;
  b.v = 4;
  __CPROVER_assert(b.load(0) == 4, "the const overload, directly");
  volatile derived vd;
  vd.v = 5;
  __CPROVER_assert(vd.load(0) == 105, "the const volatile overload");
  __CPROVER_assert(d.load(0) == 103, "WRONG (must FAIL)");
}

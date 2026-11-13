// N5008 [class.base.init]/7, [dcl.init.aggr]/4: a mem-initializer `base{x}'
// for a member of aggregate class type aggregate-initializes the member:
// its reference member binds to x.  This is initialization, not
// assignment; the aggregate's copy assignment operator is defined as
// deleted ([class.copy.assign]/7: a non-static data member of reference
// type) and takes no part.  libc++'s __tuple_leaf<I, X &&> holds such a
// member.
extern "C" void __CPROVER_assert(bool, const char *);

struct leaf
{
  int &&value;
};

struct holder
{
  leaf base;
  explicit holder(int &&x) : base{static_cast<int &&>(x)}
  {
  }
};

int main()
{
  int x = 7;
  holder h(static_cast<int &&>(x));
  __CPROVER_assert(&h.base.value == &x, "reference member bound to x");
  holder m(static_cast<holder &&>(h));
  __CPROVER_assert(m.base.value == 7, "moved");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

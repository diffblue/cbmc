// N5008 [dcl.init.aggr]/4.2, [dcl.init.general]/16.6: an element of an
// aggregate is copy-initialized from its initializer-clause; for a class
// with user-provided copy constructor and destructor that is a constructor
// call, not a copy of the bits of a temporary that is then destroyed
extern "C" void __CPROVER_assert(bool, const char *);
struct owner
{
  int *p;
  owner(int v) : p(new int(v))
  {
  }
  owner(const owner &o) : p(new int(*o.p))
  {
  }
  ~owner()
  {
    delete p;
  }
};
struct A
{
  owner o;
  int k;
};
struct B
{
  A a;
};
A make()
{
  return A{owner(6), 2};
}
int use(const A &a)
{
  return *a.o.p;
}
int main()
{
  A a{owner(5), 1};
  __CPROVER_assert(*a.o.p == 5 && a.k == 1, "member");
  B b{{owner(7), 3}};
  __CPROVER_assert(*b.a.o.p == 7, "nested");
  A m = make();
  __CPROVER_assert(*m.o.p == 6, "returned");
  __CPROVER_assert(use(A{owner(8), 4}) == 8, "temporary");
  A *h = new A{owner(9), 5};
  __CPROVER_assert(*h->o.p == 9, "new-expression");
  delete h;
  __CPROVER_assert(*a.o.p == 0, "WRONG (must FAIL)");
}

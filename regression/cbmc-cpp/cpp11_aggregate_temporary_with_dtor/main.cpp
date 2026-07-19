// N5008 [dcl.init.aggr]/1: a class is an aggregate if it has no
// user-declared or inherited constructors, no private/protected
// non-static data members, no virtual functions and no
// virtual/private/protected base classes.  A user-declared (or
// defaulted) DESTRUCTOR does not disqualify it, and
// [expr.type.conv]/2 makes `itert{&g}` aggregate-initialize a
// temporary.
//
// KNOWNBUG: as soon as a destructor is declared, CBMC resolves the
// braced functional cast `itert{&g}` through constructor overload
// resolution (which only finds the synthesized default/copy
// constructors) and fails with "found no match for symbol 'itert'".
// The same initializer works without the destructor, and the
// declaration form `itert it{&g};` works even with it.  This shape is
// libstdc++'s iterator construction in <bits/stl_tree.h> and hit the
// map-rebalance-round reducers.
//
// g++/clang++ accept and verify at runtime.  Flip to CORE when fixed.
extern "C" void __CPROVER_assert(bool, const char *);

struct nodet
{
  int v;
};

struct itert
{
  nodet *n;
  ~itert()
  {
  }
};

int main()
{
  nodet g{7};
  itert it = itert{&g};
  __CPROVER_assert(it.n == &g, "member set");
  __CPROVER_assert(it.n->v == 7, "value via member");
  return 0;
}

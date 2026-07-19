// N5008 [dcl.init.aggr]/1: a class is an aggregate if it has no
// user-declared or inherited constructors, no private/protected
// non-static data members, no virtual functions and no
// virtual/private/protected base classes.  A user-declared (or
// defaulted) DESTRUCTOR does not disqualify it, and
// [expr.type.conv]/2 makes `itert{&g}` aggregate-initialize a
// temporary.
//
// This used to fail ("found no match for symbol 'itert'"): declaring
// any destructor made the front end synthesize default/copy/move
// constructors, and the aggregate gate counted those as
// DISQUALIFYING, sending the braced temporary into constructor
// overload resolution.  Synthesized constructors are now marked
// #is_implicit_ctor and ignored by aggregate detection.
//
// g++/clang++ accept and verify at runtime.
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

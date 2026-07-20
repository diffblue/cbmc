extern "C" void __CPROVER_assert(bool, const char *);

// N5008 [stmt.return]/2 + [dcl.init.list]/3.4: `return {r}` copy-list-
// initializes the returned object; for an aggregate that is aggregate
// initialization (the member is copy-initialized from r).  CBMC's
// return path only tries CONSTRUCTOR candidates when the aggregate has
// a non-POD member (any user-declared constructor in the member's
// class), failing with "found no match for symbol 'holder'".  The same
// braced init OUTSIDE a return statement (holder h = {r};) works, as
// does the return when the member is POD.  Found dog-fooding
// src/goto-programs/restrict_function_pointers.cpp (from_options
// returns {merge(...)} into a class with a const unordered_map member).
// g++/clang++ accept and verify at runtime.

struct payload
{
  int v;
  payload() : v(0) {}
};

struct holder
{
  payload p;
};

static holder make(const payload &r)
{
  return {r}; // [stmt.return]/2: copy-list-init of holder = aggregate init
}

int main()
{
  payload r;
  r.v = 9;
  holder h = make(r);
  __CPROVER_assert(h.p.v == 9, "member preserved");
  return 0;
}

// N5008 [dcl.init.aggr]/1 + [dcl.init.list]/3 + [class.mem]: a class with a
// user-declared (converting) constructor is not an aggregate, so `It{arg}`
// calls that constructor rather than performing aggregate initialization.  When
// the argument is a reference member of the enclosing class passed as a
// temporary/return value (the shape of util/expr_iterator.h's range adapters,
// e.g. `return const_post_depth_iteratort{root};` where `root` is a
// `const exprt &` member), the reference member must be dereferenced exactly
// once.  g++/clang++ agree that begin().val() == 5.
//
// Regression: `It` has a converting constructor `It(const S&)`, so `It{root}`
// must call it; CBMC previously (a) mis-classified that constructor as a copy
// constructor and tried aggregate initialization, and (b) re-type-checked the
// already-dereferenced reference-member argument, producing an ill-formed
// double dereference `*(*this->root)` ("operand of unary * is not a pointer").
// This is the expr_iterator.h layer of the goto-cc cascade on rename_symbol.cpp.
//
// assertion.2 must FAIL, proving assertion.1 is non-vacuous.

struct S
{
  int x;
};

struct It
{
  const S &r;
  explicit It(const S &_r) : r{_r}
  {
  }
  int val() const
  {
    return r.x;
  }
};

struct range_adapter
{
  const S &root;
  explicit range_adapter(const S &_r) : root{_r}
  {
  }
  // brace-construct a temporary from the reference member, in a const method
  It begin() const
  {
    return It{root};
  }
};

extern "C" void __CPROVER_assert(int, const char *);

int main()
{
  S s{5};
  range_adapter a{s};
  __CPROVER_assert(
    a.begin().val() == 5, "brace-construct temporary from reference member");
  __CPROVER_assert(a.begin().val() != 5, "WRONG must FAIL");
  return 0;
}

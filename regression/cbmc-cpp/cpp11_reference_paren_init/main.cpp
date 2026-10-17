// N5008 [dcl.init.ref], [dcl.init]/16: a reference may be direct-initialized
// with parentheses (or braces): `T &r(init)` binds the reference exactly like
// `T &r = init`.  util/replace_symbol.cpp uses this form
// (`const exprt &const_dest(dest);`), the layer of the goto-cc cascade on
// replace_symbol.cpp reached after the incomplete-pair fix.
//
// Regression: the parser stores the parenthesized initializer as init_args (as
// for a value's direct-initialization), but a reference is not an object
// initialized by a constructor, so the object init_args path did not apply and
// the reference was reported "declared as reference but is not initialized".
// Now the single initializer is attached as the symbol value so the reference
// binding is performed.  Covers const/non-const/scalar references; g++/clang++
// agree.
//
// assertion.5 must FAIL, proving the others are non-vacuous.

struct S
{
  int x;
};

extern "C" void __CPROVER_assert(int, const char *);

int main()
{
  S s{5};
  const S &cr(s); // const reference, paren-init
  S &ncr(s);      // non-const reference, paren-init
  int i = 7;
  const int &sr(i); // scalar reference, paren-init

  __CPROVER_assert(cr.x == 5, "const reference paren-init binds to s");
  __CPROVER_assert(sr == 7, "scalar reference paren-init binds to i");
  ncr.x = 9; // mutate through the non-const reference
  __CPROVER_assert(s.x == 9, "non-const reference paren-init aliases s");
  __CPROVER_assert(cr.x == 9, "const reference sees the update through alias");
  __CPROVER_assert(cr.x == 5, "WRONG must FAIL");
  return 0;
}

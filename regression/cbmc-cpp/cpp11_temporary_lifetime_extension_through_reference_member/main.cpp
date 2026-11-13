// N5008 [class.temporary]/6: the temporary a reference is bound to persists
// for the reference's lifetime; Note 5 / Example 4: "if a temporary object
// has a reference member initialized by another temporary object, lifetime
// extension applies recursively".  Example 5: `S a{1, {2, 3}}' is fine (only
// `new S{..}' dangles, /6.11).  The inner temporary (the int the member
// binds to) was destroyed at the end of the initializer's full-expression:
// reads through r.m were dead-object dereferences.
extern "C" void __CPROVER_assert(bool, const char *);
struct R
{
  const int &m;
};
int main()
{
  const R &r = R{5};
  __CPROVER_assert(r.m == 5, "member of extended temporary");
  R r2{6};
  __CPROVER_assert(r2.m == 6, "aggregate with reference member, direct");
  const R &r3 = R{7};
  int k = r3.m;
  __CPROVER_assert(k == 7, "copy out");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

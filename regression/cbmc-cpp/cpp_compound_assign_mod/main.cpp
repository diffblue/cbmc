// Regression test for compound-assignment operator overload `%=`,
// per N5008 [over.match.oper]/3.4 + [expr.assign]/8 (compound
// assignment behaves as the corresponding non-compound operator
// followed by an assignment, but for class types looks up
// `operator%=` first).
//
// Pre-fix, the `ID_assign_mod` statement id (representing `%=`)
// was missing from the `statement → "operator%="` switch in
// `cpp_typecheckt::typecheck_side_effect_assignment` (the
// non-POD class-type path).  Compound-assignment expressions on
// non-POD class types using `%=` would emit
// "bad assignment operator 'assign_mod'" and abort.  Other
// compound-assignment operators (`+=`, `-=`, `*=`, `/=`, `<<=`,
// `>>=`, `&=`, `|=`, `^=`) were already handled.

struct BigNum
{
  int v;

  // Non-POD: user-declared destructor.
  ~BigNum() { }

  BigNum &operator%=(const BigNum &rhs)
  {
    v %= rhs.v;
    return *this;
  }
};

int main()
{
  BigNum a;
  a.v = 17;
  BigNum b;
  b.v = 5;

  a %= b;
  __CPROVER_assert(a.v == 2, "17 %= 5 leaves 2");

  return 0;
}

// N5008 [over.match.oper]/3.2: for `a @ b`, the set of member candidates is the
// result of qualified lookup of `T1::operator@`, where T1 is the type of the
// left operand.  An lvalue of reference-to-class type (e.g. the result of
// `static_cast<std::ostream &>(x)`) is an lvalue of the referenced class type,
// so the referenced class's member operator@ overloads are candidates.
//
// CBMC represents such an operand with a reference type rather than the bare
// struct_tag; the binary-operator resolution strips a leading reference before
// deciding whether the first operand has class type, so member operator@
// candidates are gathered for it.  Here mstreamt's member operator<< template
// body does `static_cast<ostream &>(base) << 42`, which must resolve to
// ostream::operator<<(int) rather than falling back to the built-in shift.
// (Regression for the residual src/util parse_options.cpp / typecheck.cpp
// dog-food "operator 'shl' not defined" noise.)
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct ostream
{
  int v = 0;
  ostream &operator<<(int n)
  {
    v = n;
    return *this;
  }
};

struct mstream
{
  ostream base;
  template <class T>
  mstream &operator<<(const T &x)
  {
    static_cast<ostream &>(base) << x; // must find ostream::operator<<(int)
    return *this;
  }
  int val() const
  {
    return base.v;
  }
};

int main()
{
  mstream ms;
  ms << 42;
  __CPROVER_assert(
    ms.val() == 42, "member operator<< found via a reference-typed operand");
  __CPROVER_assert(ms.val() != 42, "WRONG must FAIL");
  return 0;
}

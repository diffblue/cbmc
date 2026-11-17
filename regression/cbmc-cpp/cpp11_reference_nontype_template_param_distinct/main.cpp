// N5008 [temp.arg.nontype]/2 + [temp.type]/1: two class template
// specializations are the same iff their non-type reference arguments
// designate the same object.  Distinct static objects (S::a, S::b) must yield
// distinct specializations that bind to distinct objects, so rc<S::a>::val()
// == 7 and rc<S::b>::val() == 9.  g++/clang++ agree.  This verifies that the
// reference argument's object identity is preserved end-to-end (the instance
// name is built from the object, not from a valuified copy).  assertion.2 must
// FAIL, proving non-vacuity.

extern "C" void __CPROVER_assert(int, const char *);

struct S
{
  int x;
  static const S a;
  static const S b;
};
const S S::a = {7};
const S S::b = {9};

template <const S &r>
struct rc
{
  int val() const
  {
    return r.x;
  }
};

int main()
{
  rc<S::a> ra;
  rc<S::b> rb;
  __CPROVER_assert(
    ra.val() == 7 && rb.val() == 9, "distinct ref NTTPs bind distinctly");
  __CPROVER_assert(ra.val() == rb.val(), "WRONG must FAIL");
  return 0;
}

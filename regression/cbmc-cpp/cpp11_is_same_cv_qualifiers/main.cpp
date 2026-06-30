// N5008 [meta.rel]/2: is_same<T, U>::value is true iff T and U name the same
// type, INCLUDING cv-qualifiers.  So:
//   is_same<const int, int>          is FALSE
//   is_same<int, const int>          is FALSE
//   is_same<const int*, int*>        is FALSE   (nested cv differs)
//   is_same<int, int>                is TRUE
//   is_same<const int, const int>    is TRUE
// g++ and clang++ agree.
//
// KNOWN BUG: CBMC's __is_same compares the two types with irept::operator==,
// which ignores the cv-qualifier comments (#constant / #volatile), so it
// wrongly reports `const int` and `int` (and any cv-differing pair) as the
// same type.  This is the root of std::pair's converting-constructor
// constraint machinery picking the wrong _PCC<> specialization (via
// _PCCFP = conditional<!is_same<_T1,_U1> || ..., _PCC<true,...>, _PCC<false,...>>)
// for pair<const int,int>.
//
// Non-vacuous: assertion "WRONG" must FAIL.  Flip to CORE once __is_same
// distinguishes cv-qualifiers.

extern "C" void __CPROVER_assert(int, const char *);

int main()
{
  // Real properties (must hold after the fix):
  __CPROVER_assert(!__is_same(const int, int), "const int != int");
  __CPROVER_assert(!__is_same(int, const int), "int != const int");
  __CPROVER_assert(!__is_same(volatile int, int), "volatile int != int");
  __CPROVER_assert(!__is_same(const int *, int *), "const int* != int* (nested cv)");
  __CPROVER_assert(__is_same(int, int), "int == int");
  __CPROVER_assert(__is_same(const int, const int), "const int == const int");

  // Non-vacuity witness (must FAIL after the fix):
  __CPROVER_assert(__is_same(const int, int), "WRONG must FAIL");
  return 0;
}

// N5008 [over.match.copy]/1: when copy-initializing a class type T from an
// expression of class type S, a (non-explicit) conversion function of S is a
// candidate when it yields a type "whose cv-unqualified version is the same as
// T or is a derived class thereof".  Here S has `operator D()` and D derives
// from B (the target), so `B b = s;` is well-formed: s.operator D() produces a
// D prvalue, and B is then initialized from it by the derived-to-base copy
// (slicing).  g++ and clang++ accept it; b.x == 13.
//
// This was a KNOWN BUG (CBMC reported a CONVERSION ERROR) and is now fixed.
// user_defined_conversion_sequence tried the source conversion operator and
// then required standard_conversion_sequence(operator-result, T) to succeed;
// for a class prvalue of a derived type that sequence does not model the
// derived-to-base initialization, so the candidate was rejected.  Per
// [over.match.copy]/1 + [conv]/[class.derived] the operator result is now
// converted to the target base via an address-of + pointer derived-to-base
// conversion + dereference (the same mechanism the converting-constructor path
// uses).
//
// Non-vacuous: assertion 2 ("WRONG") must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

struct B
{
  int x;
  B(int v) : x(v)
  {
  }
};

struct D : B
{
  D(int v) : B(v)
  {
  }
};

struct S
{
  operator D() const
  {
    return D(13);
  }
};

int main()
{
  S s;
  B b = s; // s.operator D() -> D, then derived-to-base init of B
  __CPROVER_assert(b.x == 13, "operator D() then D->B slicing works");
  __CPROVER_assert(b.x != 13, "WRONG must FAIL");
  return 0;
}

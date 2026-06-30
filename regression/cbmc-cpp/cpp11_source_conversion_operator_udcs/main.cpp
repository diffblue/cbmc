// N5008 [over.match.copy]/1: when copy-initializing (or otherwise converting to)
// a class type T from an expression of class type S, the candidate functions
// are BOTH the converting constructors of T AND the (non-explicit) conversion
// functions of S that yield T (or a type convertible to T).  Here T has no
// constructor taking S, but S has `operator T()`, so:
//   * is_constructible<T, S> is TRUE   ([meta.unary.prop])
//   * is_convertible<S, T>   is TRUE   ([meta.unary.prop]/[conv])
// g++ and clang++ agree.
//
// KNOWN BUG: CBMC reports both FALSE.  The conversion-sequence / trait path
// (implicit_conversion_sequence -> user_defined_conversion_sequence) only
// enumerates the TARGET's converting constructors and never considers the
// SOURCE's conversion operators, so when no target constructor matches the
// source the user-defined conversion is wrongly reported as non-existent.
// (Note: ordinary overload resolution of a real call f(S)->f(T) DOES use
// S::operator T(); only the trait / conversion-sequence ranking path misses
// it, which is why this surfaces through __is_constructible /
// __is_convertible_to rather than a plain call.)
//
// Non-vacuous: assertion 3 ("WRONG") must FAIL.  Flip to CORE once
// user_defined_conversion_sequence also considers the source type's conversion
// functions per [over.match.copy]/1.

extern "C" void __CPROVER_assert(int, const char *);

struct T
{
  int x;
  T(int v) : x(v)
  {
  }
};

struct S
{
  operator T() const
  {
    return T(42);
  }
};

int main()
{
  __CPROVER_assert(__is_constructible(T, S), "T is_constructible from S via operator T()");
  __CPROVER_assert(__is_convertible_to(S, T), "S is_convertible to T via operator T()");
  __CPROVER_assert(!__is_constructible(T, S), "WRONG must FAIL");
  return 0;
}

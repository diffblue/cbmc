// N5008 [over.match.copy]/1: when copy-initializing (or otherwise converting
// to) a class type T from an expression of class type S, the candidate
// functions are BOTH the converting constructors of T AND the (non-explicit)
// conversion functions of S that yield T (or a type convertible to T).  Here T
// has no constructor taking S, but S has `operator T()`, so:
//   * is_constructible<T, S> is TRUE   ([meta.unary.prop])
//   * is_convertible<S, T>   is TRUE   ([meta.unary.prop]/[conv])
// g++ and clang++ agree.
//
// This was a KNOWN BUG and is now fixed.  user_defined_conversion_sequence does
// consider the source type's conversion functions, but binding the trait's
// synthesised declval<S>() operand to the conversion function's implicit object
// parameter (a `const S&` `this`) failed: reference_binding requires the `this`
// receiver to be an lvalue or a recognised temporary, and the synthetic
// symbol_exprt source was neither, so the candidate was discarded.  Per
// [class.mfct.non-static]/1-2 + [over.match.funcs]/5 + [class.temporary]/3 a
// class prvalue (which declval<S>() models) may be the implicit object argument
// of a member function via temporary materialization; the synthetic source is
// now marked so reference_binding materializes it.  (Ordinary overload
// resolution of a real call f(S)->f(T) already worked; only the trait /
// conversion-sequence path was affected.)
//
// Non-vacuous: assertion 3 ("WRONG") must FAIL.

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

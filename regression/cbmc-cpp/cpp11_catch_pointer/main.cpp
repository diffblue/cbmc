// N5008 [except.handle]: a handler `catch(T *)` matches a thrown pointer.  To
// build the set of exception type-ids for a handler, CBMC walks the caught
// type in cpp_exception_list_rec.  A C++ reference is represented internally as
// a pointer carrying ID_C_reference; the code extracted the pointee/referent
// type with to_reference_type in BOTH the reference and the plain-pointer
// branches.  to_reference_type asserts ID_C_reference, so for a genuine
// (non-reference) pointer handler such as `catch(int *)` its precondition
// failed:
//   Invariant check failed
//   File: .../pointer_expr.h function: to_reference_type
//   Condition: can_cast_type<reference_typet>(type)
// aborting goto-cc.  This surfaced in CBMC's own typecheck.cpp once its
// (messaget-derived) virtual dispatch stopped failing earlier.
//
// The pointee/referent type is the pointer's base type in both cases; only the
// exception-id marker differs (a genuine pointer type gets a "_ptr" suffix).
//
// Non-vacuous: assertion.2 must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

int main()
{
  int v = 7;
  int r = 0;
  try
  {
    // The handler `catch(int *)` below must type-check without aborting.  The
    // throwing path is not taken (v >= 0), so control falls through normally.
    if(v < 0)
      throw &v;
    r = v;
  }
  catch(int *p)
  {
    r = *p;
  }
  __CPROVER_assert(r == 7, "catch(int *) handler type-checks; normal path runs");
  __CPROVER_assert(r != 7, "WRONG must FAIL");
  return 0;
}

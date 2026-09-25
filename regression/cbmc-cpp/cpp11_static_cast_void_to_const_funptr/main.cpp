// N5008 [expr.static.cast]/13, [conv.qual]: a prvalue of type "pointer to cv1
// void" can be static_cast to "pointer to cv2 T" when cv2 is at least as
// cv-qualified as cv1 (it does not cast away constness).  This holds when T is
// a function pointer, so the pointee is a (const) function pointer:
//   const void* -> const FP*   where FP = int(*)(int)
//
// Bug: cast_away_constness special-cased only casts whose TARGET pointee is
// void; for a source whose pointee is void and a target pointee with a
// different subtype-chain depth -- e.g. `const FP*` (pointer -> const function
// pointer -> function), depth 3, vs `const void*`, depth 2 -- the generic
// subtype-chain comparison mis-ranked the cv-qualifiers and wrongly reported
// the cast as casting away constness, so static_cast<const FP*>(const void*)
// was rejected (CONVERSION ERROR) or produced a type-mismatched result.  This
// underlies libstdc++ std::function's _Function_base::_Base_manager::
// _M_get_pointer (`__source._M_access<_Functor*>()`).
//
// Header-free and non-vacuous (assertion 2 must FAIL).

extern "C" void __CPROVER_assert(int, const char *);

typedef int (*FP)(int);

int main()
{
  const void *v = 0;
  const FP *p = static_cast<const FP *>(v);
  __CPROVER_assert(p == 0, "static_cast void* -> const function-pointer*");
  __CPROVER_assert(p != 0, "WRONG must FAIL");
  return 0;
}

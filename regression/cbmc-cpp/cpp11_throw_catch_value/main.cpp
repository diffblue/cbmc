// N5008 [except.throw]/3-4 + [except.handle]/1-3,15: throwing an exception
// transfers control to the matching handler, and the handler's parameter is
// initialized from the exception object -- so in
//   try { throw 42; } catch(int e) { ... }
// the handler is entered with e == 42.
//
// The goto-level C++ exception lowering (remove_cpp_exceptions) turns
// CATCH-PUSH/CATCH-POP/THROW into ordinary gotos and assignments before
// symbolic execution, so control transfers to the matching `catch(int)`
// handler and e is bound to the thrown value 42.  Previously goto-symex
// stubbed symex_throw to `assume(false)` (and symex_catch to a no-op), so the
// thrown value never reached the handler and the handler body was effectively
// unreachable, making both `e == 42` and `e != 42` vacuously provable.
// assertion.2 must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

int main()
{
  try
  {
    throw 42;
  }
  catch(int e)
  {
    __CPROVER_assert(e == 42, "handler sees the thrown value");
    __CPROVER_assert(e != 42, "WRONG must FAIL");
  }
  return 0;
}

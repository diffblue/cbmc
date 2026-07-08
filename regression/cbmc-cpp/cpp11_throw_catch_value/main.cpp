// N5008 [except.throw]/3-4 + [except.handle]/1-3,15: throwing an exception
// transfers control to the matching handler, and the handler's parameter is
// initialized from the exception object -- so in
//   try { throw 42; } catch(int e) { ... }
// the handler is entered with e == 42.
//
// CBMC does not model C++ exception propagation: goto-symex's symex_throw is
// stubbed to `assume(false)` (an uncaught-exception approximation) and
// symex_catch is a no-op (both are #if 0'd out; TODO TG-4667).  As a result the
// thrown value never reaches the handler and the handler body is effectively
// unreachable, so BOTH `e == 42` and `e != 42` are vacuously provable and the
// program verifies successfully -- masking any bug in a catch handler (a
// soundness gap: handler and post-try code are never explored).
//
// A conforming model transfers control to the `catch(int)` handler and binds
// e to the thrown value 42, so `e == 42` holds (SUCCESS) and the deliberately
// wrong `e != 42` fails (FAILURE).  g++/clang++ run the handler with e == 42.
//
// KNOWN BUG: requires modelling exception control-flow transfer to the matching
// handler and initializing the handler parameter from the exception object
// (goto-symex symex_throw / symex_catch, or a goto-level exception-lowering
// pass).  Flip to CORE once the thrown value reaches the handler.
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

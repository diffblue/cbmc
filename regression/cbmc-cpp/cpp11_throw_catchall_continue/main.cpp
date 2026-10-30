// N5008 [except.handle]/1,5: `catch(...)` matches any exception; after a
// handler completes, execution continues after the try-block ([except.handle]
// /15, [except.throw]).  This exercises the goto-level C++ exception lowering:
// the throw transfers to the catch-all handler, and control then falls through
// to the statements after the try.
// assertion.2 must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

int main()
{
  int stage = 0;
  try
  {
    stage = 1;
    throw 3;
    stage = 9; // unreachable: after the throw
  }
  catch(...)
  {
    stage = 2;
  }
  // reached after the handler completes
  __CPROVER_assert(stage == 2, "catch(...) ran and control continued");
  __CPROVER_assert(stage != 2, "WRONG must FAIL");
  return 0;
}

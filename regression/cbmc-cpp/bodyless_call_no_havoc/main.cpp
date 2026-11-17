// SOUNDNESS (CBMC semantics, not a C++ conformance issue): a call to a
// function with no available body is modelled as a NO-OP, so state that
// the callee could have modified is proved unchanged.  Here `mutate` is
// declared and never defined, yet `x == 1` afterwards VERIFIES.
//   * with unwinding assertions (default) a "no body for callee"
//     property does fail, so the user is at least warned -- but the
//     assertion still succeeds, i.e. the reasoning itself is unsound;
//   * with --no-unwinding-assertions (needed by any test that bounds
//     loops) there is NO diagnostic at all and the run reports
//     VERIFICATION SUCCESSFUL.
// Expected: a missing body must not permit proving that observable
// state is unchanged (havoc the reachable state, or fail regardless of
// the unwinding-assertions setting).
// Found while diagnosing libcxx23_vector_pushback, where an odr-used
// libc++ member (__vector_layout::__relocate) ends up bodyless and the
// resulting wrong verdict is silent for exactly this reason.
// The program is intentionally not linkable (declaration only), so
// there is no runtime cross-check.
extern "C" void __CPROVER_assert(bool, const char *);
// declared, never defined anywhere in the program
void mutate(int *p);
int main()
{
  int x = 1;
  mutate(&x);
  // mutate's effect is unknown, so x may be anything: this assertion
  // must NOT be provable
  __CPROVER_assert(x == 1, "value after a call with no body must be unknown");
  return 0;
}

// Regression for an internal invariant-violation crash (not a wrong result):
// calling std::erase_if (which returns vector::size_type) and discarding the
// result used to corrupt the type of the *following* statement.
//
// std::erase_if is a system-header function template.  Its body is converted
// while main is being converted (a nested convert_function).  convert_function
// sets the type-checker's current `return_type` to the callee's return type
// (here vector<int>::size_type) and restored it only at its normal end.  When
// erase_if's body conversion threw (a separate, still-open instantiation gap)
// and the throw was caught by the system-header guard, `return_type` was left
// pointing at size_type.  main's subsequent `return 0;` was then converted
// against that stale type (N5008 [stmt.return]/3 converts the operand to the
// *enclosing* function's return type), so `0` became a 64-bit size_t while
// main's return slot stayed a 32-bit int -- a type-inconsistent assignment that
// tripped the symbolic-execution invariant lhs.type() == rhs.type() and aborted
// CBMC.
//
// The fix makes convert_function restore `return_type` (and the loop-context
// flags) on every exit, including exceptions, via a scope guard.  This test
// must complete normally without an invariant violation.  (std::erase_if's
// functional effect on the vector is exercised by the companion KNOWNBUG
// cpp20_vector_erase_if; here the call's effect is intentionally not asserted.)
#include <vector>

int main()
{
  std::vector<int> v;
  v.push_back(1);
  std::erase_if(v, [](int x) { return x == 2; });
  return 0;
}

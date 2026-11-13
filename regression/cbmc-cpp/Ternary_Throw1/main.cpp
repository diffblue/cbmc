#include <cassert>

// Regression test for a typo in cpp_typecheckt::typecheck_expr_trinary
// where the void-operand handling block was guarded by
//
//   if(expr.op1().type().id()==ID_empty ||
//      expr.op1().type().id()==ID_empty)
//
// (both disjuncts reference op1). The intent was to enter the block
// whenever EITHER operand is void; in particular, a ternary whose
// third operand is a throw expression (which has type void) should
// take the type of the second operand. Under the typo, that case
// fell through to the regular type-matching paths and produced a
// "types are incompatible" error: "I got 'signed int' and 'void'".
//
// The result of the ternary is discarded via static_cast<void>;
// goto_convert handles the discarded form by simply emitting the
// non-throw branch as an expression statement and the throw branch
// as a throw, so no goto-program assignment with mismatched lhs/rhs
// types is generated. This keeps the test compatible with the
// regression suite's --validate-goto-model profile, which does not
// currently support a ternary with a throw operand whose value is
// assigned to a variable (a separate, pre-existing issue).
//
// Both gcc and clang accept the construct below; cbmc should as
// well.

int main()
{
  int x = 5;
  bool cond = true;
  // op1 = int (non-void), op2 = throw 1 (void). Without the fix the
  // void-handling block is skipped (because both disjuncts referenced
  // op1), and typechecking ultimately fails with the
  // "types are incompatible" error. With the fix, the block is
  // entered, the throw-side handling sets the result type to op1's
  // type (int), and the expression typechecks. cond is fixed to true
  // so the throw branch is never executed at runtime.
  static_cast<void>(cond ? x : throw 1);
  assert(x == 5);

  return 0;
}

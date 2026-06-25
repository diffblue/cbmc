// a non-pointer static object, used to probe address-of below
static int sv;

int main()
{
  // GCC and Clang both constant-fold integer constant arithmetic, regardless of
  // the operator used, so __builtin_constant_p must report all of the following
  // as constant. This is checked at compile time via _Static_assert; run under
  // the ansi-c-clang profile it exercises the Clang-specific constant-folding
  // path (clang_is_constant_foldedt) in src/ansi-c/c_typecheck_expr.cpp, which
  // previously only recognised addition and multiplication.
  _Static_assert(__builtin_constant_p(1 + 1), "");
  _Static_assert(__builtin_constant_p(1 - 1), "");
  _Static_assert(__builtin_constant_p(-7), "");
  _Static_assert(__builtin_constant_p(5 * 0), "");
  _Static_assert(__builtin_constant_p(6 / 2), "");
  _Static_assert(__builtin_constant_p(7 % 3), "");
  _Static_assert(__builtin_constant_p(0 << 3), "");
  _Static_assert(__builtin_constant_p(16 >> 2), "");

  // The cases below exercise the genuinely Clang-specific branches of
  // clang_is_constant_foldedt (ternary short-circuit, &&/|| short-circuit, and
  // address-of) under the ansi-c-clang profile. CBMC produces the same results
  // in GCC mode (where __builtin_constant_p folds via the simplifier), so the
  // assertions hold under both.
  int j; // a non-constant operand

  // ternary: only the taken branch needs to be constant
  _Static_assert(__builtin_constant_p(0 ? j : 1), "");
  _Static_assert(__builtin_constant_p(1 ? 1 : j), "");
  _Static_assert(!__builtin_constant_p(1 ? j : 0), "");

  // &&/|| short-circuit: a determined result is constant; otherwise not
  _Static_assert(__builtin_constant_p(0 && j), "");
  _Static_assert(__builtin_constant_p(1 || j), "");
  _Static_assert(!__builtin_constant_p(1 && j), "");
  _Static_assert(!__builtin_constant_p(0 || j), "");

  // a string literal is constant, but the address of a static object is not
  _Static_assert(__builtin_constant_p("x"), "");
  _Static_assert(!__builtin_constant_p(&sv), "");

  return 0;
}

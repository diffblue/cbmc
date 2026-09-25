// Regression for [stmt.ranged]: `break` and `continue` are
// permitted inside the body of a range-based `for` loop.
//
// CBMC's `cpp_typecheckt::typecheck_code` lowers a range-based
// `for(decl : range) body` to a regular `for` loop, but the body
// is type-checked BEFORE the synthesised regular `for` is built.
// `c_typecheck_baset::typecheck_for` is the function that flips
// `break_is_allowed` / `continue_is_allowed` to true around its
// body type-check; the range-for lowering bypassed that flag flip,
// so a `continue;` inside a range-for body was rejected with
//
//     continue not allowed here
//
// This affected both lowering branches: the array/initializer-list
// branch (rewritten to `for(__i ...)`) and the class-typed-range
// branch (rewritten to begin/end iterator with `!=`/`++`/`*`).
// Save and set the flags before recursing into `typecheck_code(body)`
// in BOTH branches; restore on the way out.

#include <vector>

int sum_skipping(const std::vector<int> &v, int skip)
{
  int sum = 0;
  for(const auto &x : v)
  {
    if(x == skip)
      continue;
    if(x < 0)
      break;
    sum += x;
  }
  return sum;
}

int main()
{
  std::vector<int> v{1, 2, 3, 4, 5};
  int s = sum_skipping(v, 3);
  (void)s;
  return 0;
}

// Reduced from cpp20_ranges_basic_libcxx: a single call to the
// std::views::take range-adaptor object (no pipe, no range) crashes
// the C++ front end.  During guess_function_template_args a malformed
// explicit-typecast expression (nil type, TWO nil operands) reaches
// operator_is_overloaded, whose conversion-operator branch requires a
// single operand: invariant "unary expression must have one operand"
// (std_expr.h unary_exprt::check via cpp_typecheck_expr.cpp
// operator_is_overloaded).  Naming the object without calling it is
// fine.  clang++/g++ accept and run clean.
#include <ranges>

int main()
{
  auto v = std::views::take(3);
  (void)v;
  __CPROVER_assert(true, "views::take call typechecks");
  return 0;
}

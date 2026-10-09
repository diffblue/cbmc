// N5008 [stmt.return]/3 + [expr.prim.lambda]: a lambda body's return
// statements convert to the LAMBDA's return type, and the enclosing
// function's return statements convert to the ENCLOSING function's --
// the lambda's type-checking must not disturb the enclosing context.
// Pins the exception-safe return-type guard in typecheck_expr's lambda
// path (cpp_typecheck_expr.cpp): the enclosing `return 1;` below needs
// the int -> double conversion applied AFTER the int-returning lambda
// (with deduced AND explicit return types) was type-checked.
extern "C" void __CPROVER_assert(bool, const char *);
double half()
{
  auto deduced = [](int x) { return x + 41; };
  auto explicit_ret = [](int x) -> long { return x + 1; };
  __CPROVER_assert(deduced(1) == 42, "deduced-return lambda");
  __CPROVER_assert(explicit_ret(1) == 2l, "explicit-return lambda");
  return 1; // must convert to 1.0 ([conv.fpint])
}
int main()
{
  __CPROVER_assert(half() == 1.0, "enclosing return conversion intact");
  __CPROVER_assert(half() / 2.0 == 0.5, "double arithmetic on result");
  return 0;
}

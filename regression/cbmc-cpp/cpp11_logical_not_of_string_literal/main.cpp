extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  // [expr.unary.op]/9: the operand of ! is contextually converted to bool;
  // a string literal is an array that decays to a non-null pointer
  // ([conv.array], [conv.bool])
  bool b = !"unexpected state";
  __CPROVER_assert(!b, "not of a literal is false");
  __CPROVER_assert(!!"x", "double not of a literal is true");
  __CPROVER_assert(b, "WRONG (must FAIL)");
}

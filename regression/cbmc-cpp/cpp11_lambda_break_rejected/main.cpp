// N5008 [stmt.break]/1: a break statement shall be enclosed by an
// iteration statement or a switch -- within the SAME function.  A
// lambda body is a new function scope: its `break` cannot bind to a
// loop enclosing the lambda-expression.  CBMC must reject this
// (g++/clang++ do); pins that the lambda body's loop-context flags are
// isolated from the enclosing function's.
int main()
{
  for(int i = 0; i < 1; i++)
  {
    auto l = [] { break; };
    (void)l;
  }
  return 0;
}

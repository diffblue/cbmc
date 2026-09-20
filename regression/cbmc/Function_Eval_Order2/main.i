/* C99 6.5.2.2:10
 *
 * The order of evaluation of the function designator, the actual arguments,
 * and subexpressions within the actual arguments is unspecified, but there is
 * a sequence point before the actual call.
 *
 * CBMC models the fixed order that the configured compiler/architecture
 * combination uses; this test pins arm64/GCC, which evaluates left-to-right,
 * so z == 3 * 1 + 2 == 5 and the assertion of z == 7 fails. The input is a
 * preprocessed file so that no target-specific flags are passed to the native
 * preprocessor.
 */

int f00(void)
{
  static int i = 0;

  return ++i;
}

int f01(int x, int y)
{
  return 3 * x + y;
}

int main(void)
{
  int z = f01(f00(), f00());

  __CPROVER_assert(z == 7, "z == 7");

  return 1;
}

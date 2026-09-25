// -fsingle-precision-constant makes an unsuffixed floating-point constant
// `float` instead of the default `double`.  The type of such a constant is
// therefore sizeof(float) rather than sizeof(double); both sizes are
// fixed-width, so this holds on 32-bit and 64-bit targets.  The checks are
// _Static_asserts evaluated at conversion time, so if the flag is silently
// ignored (as it was before the dead-query fix in gcc_mode) the unsuffixed
// constant stays `double`, the assertions fail and conversion errors out.
_Static_assert(sizeof(1.0) == sizeof(float), "unsuffixed constant is float");
_Static_assert(
  sizeof(3.14159) == sizeof(float),
  "unsuffixed constant is float");

// An explicitly suffixed constant keeps its suffix-determined type and is
// unaffected by the flag.
_Static_assert(
  sizeof(1.0L) == sizeof(long double), "long double suffix unaffected");

int main(void)
{
  return 0;
}

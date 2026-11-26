extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  // [conv.bool]/1: arithmetic types include the floating-point types; zero
  // converts to false, any other value to true
  double d = 0.1;
  double z = 0.0;
  bool a = (bool)d;
  bool b = static_cast<bool>(z);
  bool c = d;
  float f = -0.0f;
  bool e = f;
  __CPROVER_assert(a && !b && c && !e, "explicit and implicit");
  __CPROVER_assert(d && !z, "contextual");
  double nan = z / z;
  __CPROVER_assert((bool)nan, "NaN is not zero");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

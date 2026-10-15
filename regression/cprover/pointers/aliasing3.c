int main()
{
  float f;
  int *p = (int *)&f;

  // Reads of the same address at incompatible types: f as float, *p as int.
  // The bit pattern of 1.0f is 0x3f800000, so *p == 1 must not be provable
  // from f == 1.0f: equating *p with (int)f -- a numeric conversion, not a
  // bitwise reinterpretation -- would wrongly prove this.
  if(f == 1.0f)
    __CPROVER_assert(*p == 1, "property 1"); // should fail

  return 0;
}

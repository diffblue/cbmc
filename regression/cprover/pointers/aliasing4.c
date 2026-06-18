int main()
{
  float f;
  float *p = &f;

  // Same-typed reads of the same address must still be equated; the fix for
  // cross-type reads (aliasing3) must not lose this precision.
  if(f == 1.0f)
    __CPROVER_assert(*p == 1.0f, "property 1"); // should pass

  return 0;
}

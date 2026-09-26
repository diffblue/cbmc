extern "C" void __CPROVER_assert(bool, const char *);
float pickf(float x)
{
  if(float a = x)
    return a;
  return 0.f;
}
int main()
{
  __CPROVER_assert(pickf(2.f) == 2.f, "float declaration as if condition");
  __CPROVER_assert(pickf(0.f) == 0.f, "zero is false");
  __CPROVER_assert(pickf(2.f) == 3.f, "WRONG (must FAIL)");
}

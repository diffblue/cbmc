float nondet_float(void);
double nondet_double(void);

struct S
{
  float f;
  int i;
};

union U
{
  float f;
  unsigned u;
};

union V
{
  struct S s;
  unsigned long long u;
};

int main(void)
{
  float f = nondet_float();

  union U u1;
  u1.f = f;
  __CPROVER_assert(f != 1.0f || u1.u == 0x3f800000u, "bits of 1.0f");
  __CPROVER_assert(
    f == f || (u1.u & 0x7fffffffu) > 0x7f800000u, "bits of a NaN");
  __CPROVER_assert(f != -0.0f || f != 0.0f || u1.u == 0, "fails for -0.0f");

  union V v;
  v.s.f = f;
  v.s.i = 2;
  __CPROVER_assert(
    f != 1.0f || v.u == 0x000000023f800000ull, "bits of a struct");

  return 0;
}

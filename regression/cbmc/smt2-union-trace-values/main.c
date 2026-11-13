union U
{
  float f;
  unsigned u;
};
union U nondet_U(void);

int main(void)
{
  union U a = nondet_U();
  __CPROVER_assert(a.u != 0x3f800000u, "x");
}

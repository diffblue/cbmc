typedef __CPROVER_fixedbv[64][32] __plant_typet;
extern __plant_typet A0, A1;

int main(void) {
  __CPROVER_assume(A0 == (__plant_typet)0.125);
  __CPROVER_assume(A1 == (__plant_typet)0.015625);

  const __plant_typet XXX1a=A0 * A1;
  const __plant_typet XXX2a=(__plant_typet)-1 * XXX1a;
  const __plant_typet XXX2b=-0.001953125;
  __CPROVER_assert(XXX2a==XXX2b, "");
  return 0;
}

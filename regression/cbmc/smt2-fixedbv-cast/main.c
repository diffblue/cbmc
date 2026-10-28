typedef __CPROVER_fixedbv[32][16] fix32;
typedef __CPROVER_fixedbv[16][0] fix16_nofrac;

_Bool nondet_bool(void);
enum E
{
  A = -1,
  B = 1
};
enum E nondet_enum(void);
fix16_nofrac nondet_fix16(void);

int main(void)
{
  // c_bool -> fixedbv
  _Bool b = nondet_bool();
  fix32 d1 = b;
  __CPROVER_assert(d1 == 0 || d1 == 1, "c_bool_to_fixedbv");

  // c_enum -> fixedbv
  enum E e = nondet_enum();
  __CPROVER_assume(e == A || e == B);
  fix32 d2 = e;
  __CPROVER_assert(d2 == -1 || d2 == 1, "enum_to_fixedbv");

  // fixedbv with 0 fraction bits -> int
  fix16_nofrac d3 = nondet_fix16();
  __CPROVER_assume(d3 < 5 && d3 > 2);
  int i = d3;
  __CPROVER_assert(i == 3 || i == 4, "fixedbv_no_fraction");

  return 0;
}

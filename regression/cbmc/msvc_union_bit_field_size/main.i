// With Visual Studio, the size of a union is at least the size of the declared
// type of any of its bit-fields, but bit-fields do not affect the alignment of
// the union. The expected layouts are those of Visual Studio (as implemented by
// Clang).

union S0
{
  char c[3];
  short x : 14;
};
union S1
{
  char c[5];
  int x : 3;
};
union S2
{
  char c;
  int x : 3;
};
struct S3
{
  char c;
  union S1 u;
};

union
{
  union S0 s;
  unsigned char b[sizeof(union S0)];
} G0_x = {.s = {.x = -1}};
union
{
  union S1 s;
  unsigned char b[sizeof(union S1)];
} G1_x = {.s = {.x = -1}};
union
{
  union S2 s;
  unsigned char b[sizeof(union S2)];
} G2_x = {.s = {.x = -1}};

int main(void)
{
  __CPROVER_assert(sizeof(union S0) == 3, "sizeof(union S0)");
  __CPROVER_assert(__alignof(union S0) == 1, "__alignof(union S0)");
  __CPROVER_assert(
    (unsigned long long)&((union S0 *)0)->c == 0, "offset of S0.c");
  __CPROVER_assert(
    G0_x.b[0] == 255 && G0_x.b[1] == 63 && G0_x.b[2] == 0, "bytes of S0.x");
  __CPROVER_assert(sizeof(union S1) == 5, "sizeof(union S1)");
  __CPROVER_assert(__alignof(union S1) == 1, "__alignof(union S1)");
  __CPROVER_assert(
    (unsigned long long)&((union S1 *)0)->c == 0, "offset of S1.c");
  __CPROVER_assert(
    G1_x.b[0] == 7 && G1_x.b[1] == 0 && G1_x.b[2] == 0 && G1_x.b[3] == 0 &&
      G1_x.b[4] == 0,
    "bytes of S1.x");
  __CPROVER_assert(sizeof(union S2) == 4, "sizeof(union S2)");
  __CPROVER_assert(__alignof(union S2) == 1, "__alignof(union S2)");
  __CPROVER_assert(
    (unsigned long long)&((union S2 *)0)->c == 0, "offset of S2.c");
  __CPROVER_assert(
    G2_x.b[0] == 7 && G2_x.b[1] == 0 && G2_x.b[2] == 0 && G2_x.b[3] == 0,
    "bytes of S2.x");
  __CPROVER_assert(sizeof(struct S3) == 6, "sizeof(struct S3)");
  __CPROVER_assert(__alignof(struct S3) == 1, "__alignof(struct S3)");
  __CPROVER_assert(
    (unsigned long long)&((struct S3 *)0)->c == 0, "offset of S3.c");
  __CPROVER_assert(
    (unsigned long long)&((struct S3 *)0)->u == 1, "offset of S3.u");
  return 0;
}

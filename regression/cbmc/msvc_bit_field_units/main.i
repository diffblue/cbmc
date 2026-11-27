// With Visual Studio, a bit-field that does not fit into the remaining bits of
// the unit allocated for preceding bit-fields of a type of the same size starts
// a new unit. The expected layouts are those of Visual Studio (as implemented
// by Clang).

struct S0
{
  short x : 12;
  short y : 6;
};
struct S1
{
  int x : 25;
  int y : 9;
  char c;
};
struct S2
{
  char a;
  unsigned x : 20;
  unsigned y : 13;
  unsigned z : 1;
};
struct S3
{
  long long x : 40;
  long long y : 30;
};
#pragma pack(push, 1)
struct S4
{
  char a;
  int x : 30;
  int y : 3;
};
#pragma pack(pop)

union
{
  struct S0 s;
  unsigned char b[sizeof(struct S0)];
} G0_x = {.s = {.x = -1}};
union
{
  struct S0 s;
  unsigned char b[sizeof(struct S0)];
} G0_y = {.s = {.y = -1}};
union
{
  struct S1 s;
  unsigned char b[sizeof(struct S1)];
} G1_x = {.s = {.x = -1}};
union
{
  struct S1 s;
  unsigned char b[sizeof(struct S1)];
} G1_y = {.s = {.y = -1}};
union
{
  struct S2 s;
  unsigned char b[sizeof(struct S2)];
} G2_x = {.s = {.x = -1}};
union
{
  struct S2 s;
  unsigned char b[sizeof(struct S2)];
} G2_y = {.s = {.y = -1}};
union
{
  struct S2 s;
  unsigned char b[sizeof(struct S2)];
} G2_z = {.s = {.z = -1}};
union
{
  struct S3 s;
  unsigned char b[sizeof(struct S3)];
} G3_x = {.s = {.x = -1}};
union
{
  struct S3 s;
  unsigned char b[sizeof(struct S3)];
} G3_y = {.s = {.y = -1}};
union
{
  struct S4 s;
  unsigned char b[sizeof(struct S4)];
} G4_x = {.s = {.x = -1}};
union
{
  struct S4 s;
  unsigned char b[sizeof(struct S4)];
} G4_y = {.s = {.y = -1}};

int main(void)
{
  __CPROVER_assert(sizeof(struct S0) == 4, "sizeof(struct S0)");
  __CPROVER_assert(__alignof(struct S0) == 2, "__alignof(struct S0)");
  __CPROVER_assert(
    G0_x.b[0] == 255 && G0_x.b[1] == 15 && G0_x.b[2] == 0 && G0_x.b[3] == 0,
    "bytes of S0.x");
  __CPROVER_assert(
    G0_y.b[0] == 0 && G0_y.b[1] == 0 && G0_y.b[2] == 63 && G0_y.b[3] == 0,
    "bytes of S0.y");
  __CPROVER_assert(sizeof(struct S1) == 12, "sizeof(struct S1)");
  __CPROVER_assert(__alignof(struct S1) == 4, "__alignof(struct S1)");
  __CPROVER_assert(
    (unsigned long long)&((struct S1 *)0)->c == 8, "offset of S1.c");
  __CPROVER_assert(
    G1_x.b[0] == 255 && G1_x.b[1] == 255 && G1_x.b[2] == 255 &&
      G1_x.b[3] == 1 && G1_x.b[4] == 0 && G1_x.b[5] == 0 && G1_x.b[6] == 0 &&
      G1_x.b[7] == 0 && G1_x.b[8] == 0 && G1_x.b[9] == 0 && G1_x.b[10] == 0 &&
      G1_x.b[11] == 0,
    "bytes of S1.x");
  __CPROVER_assert(
    G1_y.b[0] == 0 && G1_y.b[1] == 0 && G1_y.b[2] == 0 && G1_y.b[3] == 0 &&
      G1_y.b[4] == 255 && G1_y.b[5] == 1 && G1_y.b[6] == 0 && G1_y.b[7] == 0 &&
      G1_y.b[8] == 0 && G1_y.b[9] == 0 && G1_y.b[10] == 0 && G1_y.b[11] == 0,
    "bytes of S1.y");
  __CPROVER_assert(sizeof(struct S2) == 12, "sizeof(struct S2)");
  __CPROVER_assert(__alignof(struct S2) == 4, "__alignof(struct S2)");
  __CPROVER_assert(
    (unsigned long long)&((struct S2 *)0)->a == 0, "offset of S2.a");
  __CPROVER_assert(
    G2_x.b[0] == 0 && G2_x.b[1] == 0 && G2_x.b[2] == 0 && G2_x.b[3] == 0 &&
      G2_x.b[4] == 255 && G2_x.b[5] == 255 && G2_x.b[6] == 15 &&
      G2_x.b[7] == 0 && G2_x.b[8] == 0 && G2_x.b[9] == 0 && G2_x.b[10] == 0 &&
      G2_x.b[11] == 0,
    "bytes of S2.x");
  __CPROVER_assert(
    G2_y.b[0] == 0 && G2_y.b[1] == 0 && G2_y.b[2] == 0 && G2_y.b[3] == 0 &&
      G2_y.b[4] == 0 && G2_y.b[5] == 0 && G2_y.b[6] == 0 && G2_y.b[7] == 0 &&
      G2_y.b[8] == 255 && G2_y.b[9] == 31 && G2_y.b[10] == 0 && G2_y.b[11] == 0,
    "bytes of S2.y");
  __CPROVER_assert(
    G2_z.b[0] == 0 && G2_z.b[1] == 0 && G2_z.b[2] == 0 && G2_z.b[3] == 0 &&
      G2_z.b[4] == 0 && G2_z.b[5] == 0 && G2_z.b[6] == 0 && G2_z.b[7] == 0 &&
      G2_z.b[8] == 0 && G2_z.b[9] == 32 && G2_z.b[10] == 0 && G2_z.b[11] == 0,
    "bytes of S2.z");
  __CPROVER_assert(sizeof(struct S3) == 16, "sizeof(struct S3)");
  __CPROVER_assert(__alignof(struct S3) == 8, "__alignof(struct S3)");
  __CPROVER_assert(
    G3_x.b[0] == 255 && G3_x.b[1] == 255 && G3_x.b[2] == 255 &&
      G3_x.b[3] == 255 && G3_x.b[4] == 255 && G3_x.b[5] == 0 &&
      G3_x.b[6] == 0 && G3_x.b[7] == 0 && G3_x.b[8] == 0 && G3_x.b[9] == 0 &&
      G3_x.b[10] == 0 && G3_x.b[11] == 0 && G3_x.b[12] == 0 &&
      G3_x.b[13] == 0 && G3_x.b[14] == 0 && G3_x.b[15] == 0,
    "bytes of S3.x");
  __CPROVER_assert(
    G3_y.b[0] == 0 && G3_y.b[1] == 0 && G3_y.b[2] == 0 && G3_y.b[3] == 0 &&
      G3_y.b[4] == 0 && G3_y.b[5] == 0 && G3_y.b[6] == 0 && G3_y.b[7] == 0 &&
      G3_y.b[8] == 255 && G3_y.b[9] == 255 && G3_y.b[10] == 255 &&
      G3_y.b[11] == 63 && G3_y.b[12] == 0 && G3_y.b[13] == 0 &&
      G3_y.b[14] == 0 && G3_y.b[15] == 0,
    "bytes of S3.y");
  __CPROVER_assert(sizeof(struct S4) == 9, "sizeof(struct S4)");
  __CPROVER_assert(__alignof(struct S4) == 1, "__alignof(struct S4)");
  __CPROVER_assert(
    (unsigned long long)&((struct S4 *)0)->a == 0, "offset of S4.a");
  __CPROVER_assert(
    G4_x.b[0] == 0 && G4_x.b[1] == 255 && G4_x.b[2] == 255 &&
      G4_x.b[3] == 255 && G4_x.b[4] == 63 && G4_x.b[5] == 0 && G4_x.b[6] == 0 &&
      G4_x.b[7] == 0 && G4_x.b[8] == 0,
    "bytes of S4.x");
  __CPROVER_assert(
    G4_y.b[0] == 0 && G4_y.b[1] == 0 && G4_y.b[2] == 0 && G4_y.b[3] == 0 &&
      G4_y.b[4] == 0 && G4_y.b[5] == 7 && G4_y.b[6] == 0 && G4_y.b[7] == 0 &&
      G4_y.b[8] == 0,
    "bytes of S4.y");
  return 0;
}

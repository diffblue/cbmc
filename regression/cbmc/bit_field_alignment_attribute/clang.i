// An alignment attribute of the declaration of a bit-field, even aligned(1),
// aligns the start of the bit-field. GCC then checks whether the bit-field
// straddles a unit of its declared type, and caps the alignment at the value of
// #pragma pack. Clang checks for straddling first (using the larger of both
// alignments), and ignores attributes requesting more than #pragma pack.
// The expected layouts are those of Clang.

struct S0
{
  char a[3];
  __attribute__((aligned(2))) long long x : 37;
};
struct S1
{
  char a[3];
  char y : 4;
  __attribute__((aligned(1))) char x : 6;
};
struct S2
{
  char a[5];
  __attribute__((aligned(16))) int x : 30;
};
struct S3
{
  long long a;
  __attribute__((aligned(1))) unsigned short x : 3;
  unsigned long long y : 3;
  __attribute__((aligned(1))) int z : 5;
};
#pragma pack(push, 4)
struct S4
{
  long long a : 19;
  __attribute__((aligned(1))) short x : 1;
};
#pragma pack(pop)
#pragma pack(push, 2)
struct S5
{
  char a;
  __attribute__((aligned(4))) int x : 3;
};
#pragma pack(pop)

union
{
  struct S0 s;
  unsigned char b[sizeof(struct S0)];
} G0_x = {.s = {.x = -1}};
union
{
  struct S1 s;
  unsigned char b[sizeof(struct S1)];
} G1_y = {.s = {.y = -1}};
union
{
  struct S1 s;
  unsigned char b[sizeof(struct S1)];
} G1_x = {.s = {.x = -1}};
union
{
  struct S2 s;
  unsigned char b[sizeof(struct S2)];
} G2_x = {.s = {.x = -1}};
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
  struct S3 s;
  unsigned char b[sizeof(struct S3)];
} G3_z = {.s = {.z = -1}};
union
{
  struct S4 s;
  unsigned char b[sizeof(struct S4)];
} G4_a = {.s = {.a = -1}};
union
{
  struct S4 s;
  unsigned char b[sizeof(struct S4)];
} G4_x = {.s = {.x = -1}};
union
{
  struct S5 s;
  unsigned char b[sizeof(struct S5)];
} G5_x = {.s = {.x = -1}};

int main(void)
{
  __CPROVER_assert(sizeof(struct S0) == 16, "sizeof(struct S0)");
  __CPROVER_assert(_Alignof(struct S0) == 8, "_Alignof(struct S0)");
  __CPROVER_assert(__builtin_offsetof(struct S0, a) == 0, "offset of S0.a");
  __CPROVER_assert(
    G0_x.b[0] == 0 && G0_x.b[1] == 0 && G0_x.b[2] == 0 && G0_x.b[3] == 0 &&
      G0_x.b[4] == 255 && G0_x.b[5] == 255 && G0_x.b[6] == 255 &&
      G0_x.b[7] == 255 && G0_x.b[8] == 31 && G0_x.b[9] == 0 &&
      G0_x.b[10] == 0 && G0_x.b[11] == 0 && G0_x.b[12] == 0 &&
      G0_x.b[13] == 0 && G0_x.b[14] == 0 && G0_x.b[15] == 0,
    "bytes of S0.x");
  __CPROVER_assert(sizeof(struct S1) == 5, "sizeof(struct S1)");
  __CPROVER_assert(_Alignof(struct S1) == 1, "_Alignof(struct S1)");
  __CPROVER_assert(__builtin_offsetof(struct S1, a) == 0, "offset of S1.a");
  __CPROVER_assert(
    G1_y.b[0] == 0 && G1_y.b[1] == 0 && G1_y.b[2] == 0 && G1_y.b[3] == 15 &&
      G1_y.b[4] == 0,
    "bytes of S1.y");
  __CPROVER_assert(
    G1_x.b[0] == 0 && G1_x.b[1] == 0 && G1_x.b[2] == 0 && G1_x.b[3] == 0 &&
      G1_x.b[4] == 63,
    "bytes of S1.x");
  __CPROVER_assert(sizeof(struct S2) == 32, "sizeof(struct S2)");
  __CPROVER_assert(_Alignof(struct S2) == 16, "_Alignof(struct S2)");
  __CPROVER_assert(__builtin_offsetof(struct S2, a) == 0, "offset of S2.a");
  __CPROVER_assert(
    G2_x.b[0] == 0 && G2_x.b[1] == 0 && G2_x.b[2] == 0 && G2_x.b[3] == 0 &&
      G2_x.b[4] == 0 && G2_x.b[5] == 0 && G2_x.b[6] == 0 && G2_x.b[7] == 0 &&
      G2_x.b[8] == 0 && G2_x.b[9] == 0 && G2_x.b[10] == 0 && G2_x.b[11] == 0 &&
      G2_x.b[12] == 0 && G2_x.b[13] == 0 && G2_x.b[14] == 0 &&
      G2_x.b[15] == 0 && G2_x.b[16] == 255 && G2_x.b[17] == 255 &&
      G2_x.b[18] == 255 && G2_x.b[19] == 63 && G2_x.b[20] == 0 &&
      G2_x.b[21] == 0 && G2_x.b[22] == 0 && G2_x.b[23] == 0 &&
      G2_x.b[24] == 0 && G2_x.b[25] == 0 && G2_x.b[26] == 0 &&
      G2_x.b[27] == 0 && G2_x.b[28] == 0 && G2_x.b[29] == 0 &&
      G2_x.b[30] == 0 && G2_x.b[31] == 0,
    "bytes of S2.x");
  __CPROVER_assert(sizeof(struct S3) == 16, "sizeof(struct S3)");
  __CPROVER_assert(_Alignof(struct S3) == 8, "_Alignof(struct S3)");
  __CPROVER_assert(__builtin_offsetof(struct S3, a) == 0, "offset of S3.a");
  __CPROVER_assert(
    G3_x.b[0] == 0 && G3_x.b[1] == 0 && G3_x.b[2] == 0 && G3_x.b[3] == 0 &&
      G3_x.b[4] == 0 && G3_x.b[5] == 0 && G3_x.b[6] == 0 && G3_x.b[7] == 0 &&
      G3_x.b[8] == 7 && G3_x.b[9] == 0 && G3_x.b[10] == 0 && G3_x.b[11] == 0 &&
      G3_x.b[12] == 0 && G3_x.b[13] == 0 && G3_x.b[14] == 0 && G3_x.b[15] == 0,
    "bytes of S3.x");
  __CPROVER_assert(
    G3_y.b[0] == 0 && G3_y.b[1] == 0 && G3_y.b[2] == 0 && G3_y.b[3] == 0 &&
      G3_y.b[4] == 0 && G3_y.b[5] == 0 && G3_y.b[6] == 0 && G3_y.b[7] == 0 &&
      G3_y.b[8] == 56 && G3_y.b[9] == 0 && G3_y.b[10] == 0 && G3_y.b[11] == 0 &&
      G3_y.b[12] == 0 && G3_y.b[13] == 0 && G3_y.b[14] == 0 && G3_y.b[15] == 0,
    "bytes of S3.y");
  __CPROVER_assert(
    G3_z.b[0] == 0 && G3_z.b[1] == 0 && G3_z.b[2] == 0 && G3_z.b[3] == 0 &&
      G3_z.b[4] == 0 && G3_z.b[5] == 0 && G3_z.b[6] == 0 && G3_z.b[7] == 0 &&
      G3_z.b[8] == 0 && G3_z.b[9] == 31 && G3_z.b[10] == 0 && G3_z.b[11] == 0 &&
      G3_z.b[12] == 0 && G3_z.b[13] == 0 && G3_z.b[14] == 0 && G3_z.b[15] == 0,
    "bytes of S3.z");
  __CPROVER_assert(sizeof(struct S4) == 4, "sizeof(struct S4)");
  __CPROVER_assert(_Alignof(struct S4) == 4, "_Alignof(struct S4)");
  __CPROVER_assert(
    G4_a.b[0] == 255 && G4_a.b[1] == 255 && G4_a.b[2] == 7 && G4_a.b[3] == 0,
    "bytes of S4.a");
  __CPROVER_assert(
    G4_x.b[0] == 0 && G4_x.b[1] == 0 && G4_x.b[2] == 0 && G4_x.b[3] == 1,
    "bytes of S4.x");
  __CPROVER_assert(sizeof(struct S5) == 2, "sizeof(struct S5)");
  __CPROVER_assert(_Alignof(struct S5) == 2, "_Alignof(struct S5)");
  __CPROVER_assert(__builtin_offsetof(struct S5, a) == 0, "offset of S5.a");
  __CPROVER_assert(G5_x.b[0] == 0 && G5_x.b[1] == 7, "bytes of S5.x");
  return 0;
}

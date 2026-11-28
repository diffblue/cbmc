// A bit-field must not span more units of the alignment of its declared type
// than the type itself does: a bit-field that would straddle such a boundary
// starts at the next one. This does not apply in packed structs (S7), to
// packed bit-fields (S8), or with #pragma pack (S9). The expected layouts are
// those of GCC and Clang.

struct S0
{
  char a;
  int x : 31;
  char b;
};
struct S1
{
  char a;
  int : 31;
  char b;
};
struct S2
{
  char a[3];
  short x : 9;
  char b;
};
struct S3
{
  char a : 3;
  int x : 31;
  char b;
};
struct S4
{
  unsigned m0 : 1;
  unsigned m1 : 28;
  unsigned char m2 : 4;
};
struct S5
{
  long long x : 40;
  long long y : 40;
};
struct S6
{
  char a;
  short : 0;
  int x : 20;
  char b;
};
struct S7
{
  char a;
  int x : 31;
} __attribute__((packed));
struct S8
{
  char a;
  __attribute__((packed)) int x : 31;
};
#pragma pack(push, 2)
struct S9
{
  char a;
  int x : 31;
};
#pragma pack(pop)

union
{
  struct S0 s;
  unsigned char b[sizeof(struct S0)];
} G0_x = {.s = {.x = -1}};
union
{
  struct S2 s;
  unsigned char b[sizeof(struct S2)];
} G2_x = {.s = {.x = -1}};
union
{
  struct S3 s;
  unsigned char b[sizeof(struct S3)];
} G3_a = {.s = {.a = -1}};
union
{
  struct S3 s;
  unsigned char b[sizeof(struct S3)];
} G3_x = {.s = {.x = -1}};
union
{
  struct S4 s;
  unsigned char b[sizeof(struct S4)];
} G4_m0 = {.s = {.m0 = -1}};
union
{
  struct S4 s;
  unsigned char b[sizeof(struct S4)];
} G4_m1 = {.s = {.m1 = -1}};
union
{
  struct S4 s;
  unsigned char b[sizeof(struct S4)];
} G4_m2 = {.s = {.m2 = -1}};
union
{
  struct S5 s;
  unsigned char b[sizeof(struct S5)];
} G5_x = {.s = {.x = -1}};
union
{
  struct S5 s;
  unsigned char b[sizeof(struct S5)];
} G5_y = {.s = {.y = -1}};
union
{
  struct S6 s;
  unsigned char b[sizeof(struct S6)];
} G6_x = {.s = {.x = -1}};
union
{
  struct S7 s;
  unsigned char b[sizeof(struct S7)];
} G7_x = {.s = {.x = -1}};
union
{
  struct S8 s;
  unsigned char b[sizeof(struct S8)];
} G8_x = {.s = {.x = -1}};
union
{
  struct S9 s;
  unsigned char b[sizeof(struct S9)];
} G9_x = {.s = {.x = -1}};

int main(void)
{
  __CPROVER_assert(sizeof(struct S0) == 12, "sizeof(struct S0)");
  __CPROVER_assert(_Alignof(struct S0) == 4, "_Alignof(struct S0)");
  __CPROVER_assert(__builtin_offsetof(struct S0, a) == 0, "offset of S0.a");
  __CPROVER_assert(__builtin_offsetof(struct S0, b) == 8, "offset of S0.b");
  __CPROVER_assert(
    G0_x.b[0] == 0 && G0_x.b[1] == 0 && G0_x.b[2] == 0 && G0_x.b[3] == 0 &&
      G0_x.b[4] == 255 && G0_x.b[5] == 255 && G0_x.b[6] == 255 &&
      G0_x.b[7] == 127 && G0_x.b[8] == 0 && G0_x.b[9] == 0 && G0_x.b[10] == 0 &&
      G0_x.b[11] == 0,
    "bytes of S0.x");
  __CPROVER_assert(sizeof(struct S1) == 9, "sizeof(struct S1)");
  __CPROVER_assert(_Alignof(struct S1) == 1, "_Alignof(struct S1)");
  __CPROVER_assert(__builtin_offsetof(struct S1, a) == 0, "offset of S1.a");
  __CPROVER_assert(__builtin_offsetof(struct S1, b) == 8, "offset of S1.b");
  __CPROVER_assert(sizeof(struct S2) == 8, "sizeof(struct S2)");
  __CPROVER_assert(_Alignof(struct S2) == 2, "_Alignof(struct S2)");
  __CPROVER_assert(__builtin_offsetof(struct S2, a) == 0, "offset of S2.a");
  __CPROVER_assert(__builtin_offsetof(struct S2, b) == 6, "offset of S2.b");
  __CPROVER_assert(
    G2_x.b[0] == 0 && G2_x.b[1] == 0 && G2_x.b[2] == 0 && G2_x.b[3] == 0 &&
      G2_x.b[4] == 255 && G2_x.b[5] == 1 && G2_x.b[6] == 0 && G2_x.b[7] == 0,
    "bytes of S2.x");
  __CPROVER_assert(sizeof(struct S3) == 12, "sizeof(struct S3)");
  __CPROVER_assert(_Alignof(struct S3) == 4, "_Alignof(struct S3)");
  __CPROVER_assert(__builtin_offsetof(struct S3, b) == 8, "offset of S3.b");
  __CPROVER_assert(
    G3_a.b[0] == 7 && G3_a.b[1] == 0 && G3_a.b[2] == 0 && G3_a.b[3] == 0 &&
      G3_a.b[4] == 0 && G3_a.b[5] == 0 && G3_a.b[6] == 0 && G3_a.b[7] == 0 &&
      G3_a.b[8] == 0 && G3_a.b[9] == 0 && G3_a.b[10] == 0 && G3_a.b[11] == 0,
    "bytes of S3.a");
  __CPROVER_assert(
    G3_x.b[0] == 0 && G3_x.b[1] == 0 && G3_x.b[2] == 0 && G3_x.b[3] == 0 &&
      G3_x.b[4] == 255 && G3_x.b[5] == 255 && G3_x.b[6] == 255 &&
      G3_x.b[7] == 127 && G3_x.b[8] == 0 && G3_x.b[9] == 0 && G3_x.b[10] == 0 &&
      G3_x.b[11] == 0,
    "bytes of S3.x");
  __CPROVER_assert(sizeof(struct S4) == 8, "sizeof(struct S4)");
  __CPROVER_assert(_Alignof(struct S4) == 4, "_Alignof(struct S4)");
  __CPROVER_assert(
    G4_m0.b[0] == 1 && G4_m0.b[1] == 0 && G4_m0.b[2] == 0 && G4_m0.b[3] == 0 &&
      G4_m0.b[4] == 0 && G4_m0.b[5] == 0 && G4_m0.b[6] == 0 && G4_m0.b[7] == 0,
    "bytes of S4.m0");
  __CPROVER_assert(
    G4_m1.b[0] == 254 && G4_m1.b[1] == 255 && G4_m1.b[2] == 255 &&
      G4_m1.b[3] == 31 && G4_m1.b[4] == 0 && G4_m1.b[5] == 0 &&
      G4_m1.b[6] == 0 && G4_m1.b[7] == 0,
    "bytes of S4.m1");
  __CPROVER_assert(
    G4_m2.b[0] == 0 && G4_m2.b[1] == 0 && G4_m2.b[2] == 0 && G4_m2.b[3] == 0 &&
      G4_m2.b[4] == 15 && G4_m2.b[5] == 0 && G4_m2.b[6] == 0 && G4_m2.b[7] == 0,
    "bytes of S4.m2");
  __CPROVER_assert(sizeof(struct S5) == 16, "sizeof(struct S5)");
  __CPROVER_assert(_Alignof(struct S5) == 8, "_Alignof(struct S5)");
  __CPROVER_assert(
    G5_x.b[0] == 255 && G5_x.b[1] == 255 && G5_x.b[2] == 255 &&
      G5_x.b[3] == 255 && G5_x.b[4] == 255 && G5_x.b[5] == 0 &&
      G5_x.b[6] == 0 && G5_x.b[7] == 0 && G5_x.b[8] == 0 && G5_x.b[9] == 0 &&
      G5_x.b[10] == 0 && G5_x.b[11] == 0 && G5_x.b[12] == 0 &&
      G5_x.b[13] == 0 && G5_x.b[14] == 0 && G5_x.b[15] == 0,
    "bytes of S5.x");
  __CPROVER_assert(
    G5_y.b[0] == 0 && G5_y.b[1] == 0 && G5_y.b[2] == 0 && G5_y.b[3] == 0 &&
      G5_y.b[4] == 0 && G5_y.b[5] == 0 && G5_y.b[6] == 0 && G5_y.b[7] == 0 &&
      G5_y.b[8] == 255 && G5_y.b[9] == 255 && G5_y.b[10] == 255 &&
      G5_y.b[11] == 255 && G5_y.b[12] == 255 && G5_y.b[13] == 0 &&
      G5_y.b[14] == 0 && G5_y.b[15] == 0,
    "bytes of S5.y");
  __CPROVER_assert(sizeof(struct S6) == 8, "sizeof(struct S6)");
  __CPROVER_assert(_Alignof(struct S6) == 4, "_Alignof(struct S6)");
  __CPROVER_assert(__builtin_offsetof(struct S6, a) == 0, "offset of S6.a");
  __CPROVER_assert(__builtin_offsetof(struct S6, b) == 7, "offset of S6.b");
  __CPROVER_assert(
    G6_x.b[0] == 0 && G6_x.b[1] == 0 && G6_x.b[2] == 0 && G6_x.b[3] == 0 &&
      G6_x.b[4] == 255 && G6_x.b[5] == 255 && G6_x.b[6] == 15 && G6_x.b[7] == 0,
    "bytes of S6.x");
  __CPROVER_assert(sizeof(struct S7) == 5, "sizeof(struct S7)");
  __CPROVER_assert(_Alignof(struct S7) == 1, "_Alignof(struct S7)");
  __CPROVER_assert(__builtin_offsetof(struct S7, a) == 0, "offset of S7.a");
  __CPROVER_assert(
    G7_x.b[0] == 0 && G7_x.b[1] == 255 && G7_x.b[2] == 255 &&
      G7_x.b[3] == 255 && G7_x.b[4] == 127,
    "bytes of S7.x");
  __CPROVER_assert(sizeof(struct S8) == 5, "sizeof(struct S8)");
  __CPROVER_assert(_Alignof(struct S8) == 1, "_Alignof(struct S8)");
  __CPROVER_assert(__builtin_offsetof(struct S8, a) == 0, "offset of S8.a");
  __CPROVER_assert(
    G8_x.b[0] == 0 && G8_x.b[1] == 255 && G8_x.b[2] == 255 &&
      G8_x.b[3] == 255 && G8_x.b[4] == 127,
    "bytes of S8.x");
  __CPROVER_assert(sizeof(struct S9) == 6, "sizeof(struct S9)");
  __CPROVER_assert(_Alignof(struct S9) == 2, "_Alignof(struct S9)");
  __CPROVER_assert(__builtin_offsetof(struct S9, a) == 0, "offset of S9.a");
  __CPROVER_assert(
    G9_x.b[0] == 0 && G9_x.b[1] == 255 && G9_x.b[2] == 255 &&
      G9_x.b[3] == 255 && G9_x.b[4] == 127 && G9_x.b[5] == 0,
    "bytes of S9.x");
  return 0;
}

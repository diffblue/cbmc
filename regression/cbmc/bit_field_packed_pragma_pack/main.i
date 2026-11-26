// #pragma pack(n) takes precedence over a packed attribute of the declaration
// of a bit-field: the alignment of the bit-field is that of its declared type,
// capped at n (S0 to S2), rather than one (as without #pragma pack, S3). The
// expected layouts are those of GCC and Clang.

#pragma pack(push, 4)
struct S0
{
  __attribute__((packed)) int m : 3;
};
#pragma pack(pop)
#pragma pack(push, 2)
struct S1
{
  __attribute__((packed)) unsigned short m0 : 1;
  char m1;
  char m2 : 3;
};
#pragma pack(pop)
#pragma pack(push, 4)
struct S2
{
  char c;
  __attribute__((packed)) long long m : 43;
  unsigned char n : 4;
};
#pragma pack(pop)
struct S3
{
  char c;
  __attribute__((packed)) int m : 3;
};

union
{
  struct S0 s;
  unsigned char b[sizeof(struct S0)];
} G0_m = {.s = {.m = -1}};
union
{
  struct S1 s;
  unsigned char b[sizeof(struct S1)];
} G1_m0 = {.s = {.m0 = -1}};
union
{
  struct S1 s;
  unsigned char b[sizeof(struct S1)];
} G1_m2 = {.s = {.m2 = -1}};
union
{
  struct S2 s;
  unsigned char b[sizeof(struct S2)];
} G2_m = {.s = {.m = -1}};
union
{
  struct S2 s;
  unsigned char b[sizeof(struct S2)];
} G2_n = {.s = {.n = -1}};
union
{
  struct S3 s;
  unsigned char b[sizeof(struct S3)];
} G3_m = {.s = {.m = -1}};

int main(void)
{
  __CPROVER_assert(sizeof(struct S0) == 4, "sizeof(struct S0)");
  __CPROVER_assert(_Alignof(struct S0) == 4, "_Alignof(struct S0)");
  __CPROVER_assert(
    G0_m.b[0] == 7 && G0_m.b[1] == 0 && G0_m.b[2] == 0 && G0_m.b[3] == 0,
    "bytes of S0.m");
  __CPROVER_assert(sizeof(struct S1) == 4, "sizeof(struct S1)");
  __CPROVER_assert(_Alignof(struct S1) == 2, "_Alignof(struct S1)");
  __CPROVER_assert(__builtin_offsetof(struct S1, m1) == 1, "offset of S1.m1");
  __CPROVER_assert(
    G1_m0.b[0] == 1 && G1_m0.b[1] == 0 && G1_m0.b[2] == 0 && G1_m0.b[3] == 0,
    "bytes of S1.m0");
  __CPROVER_assert(
    G1_m2.b[0] == 0 && G1_m2.b[1] == 0 && G1_m2.b[2] == 7 && G1_m2.b[3] == 0,
    "bytes of S1.m2");
  __CPROVER_assert(sizeof(struct S2) == 8, "sizeof(struct S2)");
  __CPROVER_assert(_Alignof(struct S2) == 4, "_Alignof(struct S2)");
  __CPROVER_assert(__builtin_offsetof(struct S2, c) == 0, "offset of S2.c");
  __CPROVER_assert(
    G2_m.b[0] == 0 && G2_m.b[1] == 255 && G2_m.b[2] == 255 &&
      G2_m.b[3] == 255 && G2_m.b[4] == 255 && G2_m.b[5] == 255 &&
      G2_m.b[6] == 7 && G2_m.b[7] == 0,
    "bytes of S2.m");
  __CPROVER_assert(
    G2_n.b[0] == 0 && G2_n.b[1] == 0 && G2_n.b[2] == 0 && G2_n.b[3] == 0 &&
      G2_n.b[4] == 0 && G2_n.b[5] == 0 && G2_n.b[6] == 120 && G2_n.b[7] == 0,
    "bytes of S2.n");
  __CPROVER_assert(sizeof(struct S3) == 2, "sizeof(struct S3)");
  __CPROVER_assert(_Alignof(struct S3) == 1, "_Alignof(struct S3)");
  __CPROVER_assert(__builtin_offsetof(struct S3, c) == 0, "offset of S3.c");
  __CPROVER_assert(G3_m.b[0] == 0 && G3_m.b[1] == 7, "bytes of S3.m");
  return 0;
}

// With Visual Studio, a zero-width bit-field is ignored unless it follows a
// bit-field of non-zero width. Otherwise, it ends the unit of the preceding
// bit-field and aligns the next member to its declared type in a struct, and
// makes the size of a union at least the size of its declared type. The
// expected layouts are those of Visual Studio (as implemented by Clang).

struct S0
{
  char a;
  unsigned : 0;
  char b;
};
struct S1
{
  int : 0;
  char c;
};
struct S2
{
  char a;
  int : 0;
};
struct S3
{
  char x : 3;
  int : 0;
  char b;
};
struct S4
{
  int x : 3;
  int : 0;
  long long : 0;
  int y : 2;
};
union S5
{
  char c;
  int : 0;
};
union S6
{
  char x : 3;
  int : 0;
};

union
{
  struct S3 s;
  unsigned char b[sizeof(struct S3)];
} G3_x = {.s = {.x = -1}};
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
union
{
  union S6 s;
  unsigned char b[sizeof(union S6)];
} G6_x = {.s = {.x = -1}};

int main(void)
{
  __CPROVER_assert(sizeof(struct S0) == 2, "sizeof(struct S0)");
  __CPROVER_assert(__alignof(struct S0) == 1, "__alignof(struct S0)");
  __CPROVER_assert(
    (unsigned long long)&((struct S0 *)0)->a == 0, "offset of S0.a");
  __CPROVER_assert(
    (unsigned long long)&((struct S0 *)0)->b == 1, "offset of S0.b");
  __CPROVER_assert(sizeof(struct S1) == 1, "sizeof(struct S1)");
  __CPROVER_assert(__alignof(struct S1) == 1, "__alignof(struct S1)");
  __CPROVER_assert(
    (unsigned long long)&((struct S1 *)0)->c == 0, "offset of S1.c");
  __CPROVER_assert(sizeof(struct S2) == 1, "sizeof(struct S2)");
  __CPROVER_assert(__alignof(struct S2) == 1, "__alignof(struct S2)");
  __CPROVER_assert(
    (unsigned long long)&((struct S2 *)0)->a == 0, "offset of S2.a");
  __CPROVER_assert(sizeof(struct S3) == 8, "sizeof(struct S3)");
  __CPROVER_assert(__alignof(struct S3) == 4, "__alignof(struct S3)");
  __CPROVER_assert(
    (unsigned long long)&((struct S3 *)0)->b == 4, "offset of S3.b");
  __CPROVER_assert(
    G3_x.b[0] == 7 && G3_x.b[1] == 0 && G3_x.b[2] == 0 && G3_x.b[3] == 0 &&
      G3_x.b[4] == 0 && G3_x.b[5] == 0 && G3_x.b[6] == 0 && G3_x.b[7] == 0,
    "bytes of S3.x");
  __CPROVER_assert(sizeof(struct S4) == 8, "sizeof(struct S4)");
  __CPROVER_assert(__alignof(struct S4) == 4, "__alignof(struct S4)");
  __CPROVER_assert(
    G4_x.b[0] == 7 && G4_x.b[1] == 0 && G4_x.b[2] == 0 && G4_x.b[3] == 0 &&
      G4_x.b[4] == 0 && G4_x.b[5] == 0 && G4_x.b[6] == 0 && G4_x.b[7] == 0,
    "bytes of S4.x");
  __CPROVER_assert(
    G4_y.b[0] == 0 && G4_y.b[1] == 0 && G4_y.b[2] == 0 && G4_y.b[3] == 0 &&
      G4_y.b[4] == 3 && G4_y.b[5] == 0 && G4_y.b[6] == 0 && G4_y.b[7] == 0,
    "bytes of S4.y");
  __CPROVER_assert(sizeof(union S5) == 1, "sizeof(union S5)");
  __CPROVER_assert(__alignof(union S5) == 1, "__alignof(union S5)");
  __CPROVER_assert(
    (unsigned long long)&((union S5 *)0)->c == 0, "offset of S5.c");
  __CPROVER_assert(sizeof(union S6) == 4, "sizeof(union S6)");
  __CPROVER_assert(__alignof(union S6) == 1, "__alignof(union S6)");
  __CPROVER_assert(
    G6_x.b[0] == 7 && G6_x.b[1] == 0 && G6_x.b[2] == 0 && G6_x.b[3] == 0,
    "bytes of S6.x");
  return 0;
}

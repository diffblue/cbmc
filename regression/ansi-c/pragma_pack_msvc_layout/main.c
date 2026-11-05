// Visual Studio specifics of struct and union layout, as observed with
// MSVC x64 v19.

// The trailing padding is capped by the #pragma pack in effect at the end of
// the definition, whereas the alignment is not.
struct A
{
  char m0;
  double m1;
#pragma pack(push, 2)
  char m2;
};
#pragma pack(pop)
struct C
{
  char m0;
  double m1;
#pragma pack(push, 1)
  char m2;
};
#pragma pack(pop)

_Static_assert(sizeof(struct A) == 18 && __alignof(struct A) == 8, "A");
_Static_assert(sizeof(struct C) == 17 && __alignof(struct C) == 8, "C");

// #pragma pack does not reduce alignment required by __declspec(align(n))
struct __declspec(align(16)) X16
{
  char c;
};
#pragma pack(push, 1)
struct __declspec(align(16)) B
{
  char m0;
  double m1;
};
#pragma pack(pop)
struct D
{
  struct X16 x;
  char m0;
#pragma pack(push, 1)
  char m2;
};
#pragma pack(pop)
#pragma pack(push, 1)
struct E
{
  char m0;
  struct X16 x;
  char m2;
};
#pragma pack(pop)

_Static_assert(sizeof(struct B) == 16 && __alignof(struct B) == 16, "B");
_Static_assert(sizeof(struct D) == 32 && __alignof(struct D) == 16, "D");
_Static_assert(sizeof(struct E) == 48 && __alignof(struct E) == 16, "E");
_Static_assert((unsigned long long)&((struct E *)0)->x == 16, "E.x");

// also when __declspec(align(n)) applies via a typedef
struct X1
{
  char c;
};
typedef __declspec(align(16)) struct X1 TX16;
#pragma pack(push, 1)
struct G
{
  char a;
  TX16 b;
};
#pragma pack(pop)

_Static_assert(sizeof(struct G) == 32 && __alignof(struct G) == 16, "G");

// bit-fields do not affect the alignment of a union, but its size
union U1
{
  int m0 : 7;
};
union U2
{
  long m0 : 1;
  short m1;
};
union F
{
  char m0[3];
#pragma pack(push, 2)
  double d;
};
#pragma pack(pop)

_Static_assert(sizeof(union U1) == 4 && __alignof(union U1) == 1, "U1");
_Static_assert(sizeof(union U2) == 4 && __alignof(union U2) == 2, "U2");
_Static_assert(sizeof(union F) == 8 && __alignof(union F) == 2, "F");

int main()
{
  return 0;
}

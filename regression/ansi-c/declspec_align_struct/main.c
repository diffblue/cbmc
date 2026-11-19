// __declspec(align(n)) on a struct or union definition sets its alignment

struct __declspec(align(8)) S1
{
  char m0;
  char m1;
};
union __declspec(align(16)) U1
{
  int m0;
};
struct __declspec(align(32)) S2
{
  char m0;
  void *m1;
};
struct S3
{
  char c;
  struct S1 m;
};

_Static_assert(sizeof(struct S1) == 8, "");
_Static_assert(__alignof(struct S1) == 8, "");
_Static_assert(sizeof(union U1) == 16, "");
_Static_assert(__alignof(union U1) == 16, "");
_Static_assert(sizeof(struct S2) == 32, "");
_Static_assert(__alignof(struct S2) == 32, "");
_Static_assert(sizeof(struct S3) == 16, "");

// in any other position of a declaration that defines a struct or union, it
// applies to both the type and the declared entity, unless the type has an
// alignment of its own
__declspec(align(8)) struct S4
{
  char c;
};
__declspec(align(16)) union U4
{
  char c;
} u4;
typedef __declspec(align(16)) struct S5
{
  char c;
} *TP5;
const __declspec(align(16)) struct S6
{
  char c;
} s6;
__declspec(align(16)) struct __declspec(align(4)) S7
{
  char c;
} s7;
__declspec(align(16)) struct S7 s7b;

_Static_assert(sizeof(struct S4) == 8, "");
_Static_assert(sizeof(union U4) == 16, "");
_Static_assert(sizeof(struct S5) == 16 && __alignof(TP5) == 16, "");
_Static_assert(sizeof(struct S6) == 16, "");
_Static_assert(sizeof(struct S7) == 4 && __alignof(s7) == 16, "");
_Static_assert(__alignof(s7b) == 16, "");

int main()
{
  return 0;
}

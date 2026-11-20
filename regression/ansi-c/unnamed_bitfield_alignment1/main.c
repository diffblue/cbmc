// System V ABI: "Unnamed bit-fields' types do not affect the alignment of a
// structure or union." The Visual Studio ABI differs.
struct S
{
  char c;
  int : 0;
  char d;
};

struct A
{
  char c;
  int : 4;
};

struct B
{
  char a;
  long long : 3;
  char b;
};

union U
{
  char c;
  int : 4;
};

#ifndef _MSC_VER
_Static_assert(sizeof(struct S) == 5, "sizeof(struct S)");
_Static_assert(_Alignof(struct S) == 1, "_Alignof(struct S)");
_Static_assert(sizeof(struct A) == 2, "sizeof(struct A)");
_Static_assert(_Alignof(struct A) == 1, "_Alignof(struct A)");
_Static_assert(sizeof(struct B) == 3, "sizeof(struct B)");
_Static_assert(sizeof(union U) == 1, "sizeof(union U)");
#endif

int main(void)
{
  return 0;
}

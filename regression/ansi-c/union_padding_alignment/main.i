// A union is padded to a multiple of its alignment by a padding member that
// spans the entire union. That padding member must not determine the alignment
// of the union.
union U5
{
  char c[5];
  int i;
};

union U3
{
  char c[3];
  short s;
};

union U6
{
  char c[5];
  short s;
};

struct S
{
  char c;
  union U5 u;
};

_Static_assert(sizeof(union U5) == 8, "sizeof(union U5)");
_Static_assert(_Alignof(union U5) == 4, "_Alignof(union U5)");
_Static_assert(sizeof(union U3) == 4, "sizeof(union U3)");
_Static_assert(_Alignof(union U3) == 2, "_Alignof(union U3)");
_Static_assert(sizeof(union U6) == 6, "sizeof(union U6)");
_Static_assert(_Alignof(union U6) == 2, "_Alignof(union U6)");
_Static_assert(sizeof(struct S) == 12, "sizeof(struct S)");

int main(void)
{
  return 0;
}

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

int main()
{
  return 0;
}

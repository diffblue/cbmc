// Visual Studio does not let __declspec(align(n)) reduce an alignment
typedef __declspec(align(2)) int T2;
struct __declspec(align(1)) S1
{
  int i;
};
struct M1
{
  char c;
  __declspec(align(2)) int i;
};
__declspec(align(2)) int x1;

_Static_assert(__alignof(T2) == 4, "T2");
_Static_assert(__alignof(struct S1) == 4, "S1");
_Static_assert(sizeof(struct M1) == 8, "M1");
_Static_assert(__alignof(x1) == 4, "x1");

// Visual Studio uses the last of several align declspecs, in all positions
__declspec(align(16)) __declspec(align(4)) int x2;
__declspec(align(4)) __declspec(align(16)) int x3;
__declspec(align(16)) __declspec(align(2)) int x4;
struct __declspec(align(16)) __declspec(align(4)) S2
{
  char c;
};
struct __declspec(align(4)) __declspec(align(16)) S3
{
  char c;
};
__declspec(align(16)) __declspec(align(8)) struct S4
{
  char c;
};
struct M2
{
  char c;
  __declspec(align(16)) __declspec(align(4)) int i;
};
typedef __declspec(align(16)) __declspec(align(8)) int T3;

_Static_assert(__alignof(x2) == 4, "x2");
_Static_assert(__alignof(x3) == 16, "x3");
_Static_assert(__alignof(x4) == 4, "x4");
_Static_assert(__alignof(struct S2) == 4, "S2");
_Static_assert(__alignof(struct S3) == 16, "S3");
_Static_assert(__alignof(struct S4) == 8, "S4");
_Static_assert(sizeof(struct M2) == 8, "M2");
_Static_assert(__alignof(T3) == 8, "T3");

int main()
{
  return 0;
}

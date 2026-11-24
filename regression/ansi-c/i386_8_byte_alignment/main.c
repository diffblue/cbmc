// The System V ABI for i386 aligns 8-byte scalars to 4 bytes, which is what
// _Alignof reports, whereas __alignof__ reports their preferred alignment of 8.
struct S
{
  char c;
  double d;
  long long ll;
};
struct T
{
  char c;
  double a[2];
};
struct C
{
  char c;
  _Complex double z;
};
typedef double DA[2];
typedef double D4 __attribute__((aligned(4)));
double gd;
long long gll;
struct S gs;

_Static_assert(__builtin_offsetof(struct S, d) == 4, "");
_Static_assert(__builtin_offsetof(struct S, ll) == 12, "");
_Static_assert(sizeof(struct S) == 20, "");
_Static_assert(_Alignof(struct S) == 4 && __alignof__(struct S) == 4, "");
_Static_assert(__builtin_offsetof(struct T, a) == 4, "");
_Static_assert(__builtin_offsetof(struct C, z) == 4, "");

// the alignment requirement
_Static_assert(_Alignof(double) == 4 && _Alignof(long long) == 4, "");
_Static_assert(_Alignof(unsigned long long) == 4, "");
_Static_assert(_Alignof(_Complex double) == 4 && _Alignof(DA) == 4, "");

// the preferred alignment, unless an explicit alignment applies
_Static_assert(__alignof__(double) == 8 && __alignof__(long long) == 8, "");
_Static_assert(__alignof__(_Complex double) == 8 && __alignof__(DA) == 8, "");
_Static_assert(__alignof__(long double) == 4 && __alignof__(D4) == 4, "");

// objects have their preferred alignment, members their alignment requirement
_Static_assert(__alignof__(gd) == 8 && __alignof__(gll) == 8, "");
_Static_assert(__alignof__(gs.d) == 4 && _Alignof(gs.ll) == 4, "");

int main()
{
  return 0;
}

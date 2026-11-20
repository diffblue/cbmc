// The alignment that the declaration of an object or member requests applies
// to that object or member only, not to expressions computed from it. GCC,
// however, folds the dereference of the address of an object to that object,
// and, for a dereferenced pointer, uses the largest alignment of the pointee
// types of the pointer and of any pointers it was converted from. Clang only
// considers the operand as written.

int x __attribute__((aligned(16)));
int arr[4] __attribute__((aligned(32)));
struct X
{
  char c;
  int m __attribute__((aligned(16)));
} sx, *psx;
int *__attribute__((aligned(16))) pd;

// GCC and Clang agree on these
_Static_assert(__alignof__(x) == 16, "");
_Static_assert(__alignof__((x)) == 16, "");
_Static_assert(__alignof__(x + 0) == 4, "");
_Static_assert(__alignof__(+x) == 4, "");
_Static_assert(__alignof__((int)x) == 4, "");
_Static_assert(__alignof__((0, x)) == 4, "");
_Static_assert(__alignof__(&x) == sizeof(void *), "");
_Static_assert(__alignof__(arr) == 32, "");
_Static_assert(__alignof__(arr[0]) == 4, "");
_Static_assert(__alignof__(*arr) == 4, "");
_Static_assert(__alignof__(sx.m) == 16, "");
_Static_assert(__alignof__(sx.m + 0) == 4, "");
_Static_assert(__alignof__(psx->m) == 16, "");
_Static_assert(__alignof__((&sx)->m) == 16, "");
_Static_assert(__alignof__(*&sx) == 16, "");
_Static_assert(__alignof__(pd) == 16, "");

#ifdef __clang__
_Static_assert(__alignof__(*&x) == 4, "");
_Static_assert(__alignof__(*&*&x) == 4, "");
_Static_assert(__alignof__(*(&x + 0)) == 4, "");
_Static_assert(__alignof__(*(int *)&x) == 4, "");
_Static_assert(__alignof__(*(char *)&x) == 1, "");
_Static_assert(__alignof__(*&arr) == 4, "");
_Static_assert(__alignof__(*&sx.m) == 4, "");
_Static_assert(__alignof__(*&pd) == sizeof(void *), "");
#else
_Static_assert(__alignof__(*&x) == 16, "");
_Static_assert(__alignof__(*&*&x) == 16, "");
_Static_assert(__alignof__(*(&x + 0)) == 16, "");
_Static_assert(__alignof__(*(int *)&x) == 16, "");
_Static_assert(__alignof__(*(char *)&x) == 4, "");
_Static_assert(__alignof__(*&arr) == 32, "");
_Static_assert(__alignof__(*&sx.m) == 16, "");
_Static_assert(__alignof__(*&pd) == 16, "");
#endif

int main()
{
  return 0;
}

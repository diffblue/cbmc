// Packed and aligned attributes between the struct/union keyword and the tag
// of a declaration without body: GCC ignores them, while Clang applies them to
// the type when it is not complete yet (and ignores them, with a warning,
// otherwise).

#ifdef __clang__
#  define CLANG_OR_GCC(clang, gcc) (clang)
#else
#  define CLANG_OR_GCC(clang, gcc) (gcc)
#endif

// a forward declaration
struct __attribute__((aligned(16))) A1;
struct A1
{
  char c;
};
_Static_assert(_Alignof(struct A1) == CLANG_OR_GCC(16, 1), "");
_Static_assert(sizeof(struct A1) == CLANG_OR_GCC(16, 1), "");

union __attribute__((aligned(16))) A2;
union A2
{
  char c;
};
_Static_assert(_Alignof(union A2) == CLANG_OR_GCC(16, 1), "");

struct __attribute__((packed)) A3;
struct A3
{
  char c;
  int i;
};
_Static_assert(sizeof(struct A3) == CLANG_OR_GCC(5, 8), "");

struct __attribute__((packed, aligned(2))) A4;
struct A4
{
  char c;
  int i;
};
_Static_assert(sizeof(struct A4) == CLANG_OR_GCC(6, 8), "");

// with Clang, the largest alignment of all declarations applies
struct __attribute__((aligned(8))) A5;
struct __attribute__((aligned(16))) A5;
struct __attribute__((aligned(4))) A5
{
  char c;
};
_Static_assert(_Alignof(struct A5) == CLANG_OR_GCC(16, 4), "");

struct __attribute__((aligned(4))) A6;
struct A6
{
  char c;
} __attribute__((aligned(2)));
_Static_assert(_Alignof(struct A6) == CLANG_OR_GCC(4, 2), "");

struct __attribute__((aligned(16))) A7;
struct __attribute__((packed)) A7
{
  char c;
  int i;
};
_Static_assert(sizeof(struct A7) == CLANG_OR_GCC(16, 5), "");

// a declaration of an object, member, or typedef that refers to a type that
// is not complete yet
struct __attribute__((aligned(16))) B1 *b1;
struct B1
{
  char c;
};
_Static_assert(__alignof__(b1) == sizeof(void *), "");
_Static_assert(_Alignof(struct B1) == CLANG_OR_GCC(16, 1), "");

struct B2
{
  char c;
  struct __attribute__((aligned(16))) B3 *p;
};
struct B3
{
  char c;
};
_Static_assert(sizeof(struct B2) == 2 * sizeof(void *), "");
_Static_assert(_Alignof(struct B3) == CLANG_OR_GCC(16, 1), "");

typedef struct __attribute__((aligned(16))) B4 TB4;
struct B4
{
  char c;
};
_Static_assert(_Alignof(TB4) == CLANG_OR_GCC(16, 1), "");

// a block-scope declaration
void f(void)
{
  struct __attribute__((aligned(16))) C1;
  struct C1
  {
    char c;
  };
  _Static_assert(_Alignof(struct C1) == CLANG_OR_GCC(16, 1), "");
}
struct C1
{
  char c;
};
_Static_assert(_Alignof(struct C1) == 1, "");

// once the type is complete, both ignore them
struct F
{
  char c;
  int i;
};
struct __attribute__((aligned(16))) F;
struct __attribute__((aligned(16))) F f1;
struct __attribute__((aligned(16))) F *pf;
struct __attribute__((packed)) F f2;
struct M
{
  char c;
  struct __attribute__((aligned(16))) F m;
};
_Static_assert(_Alignof(struct F) == 4, "");
_Static_assert(__alignof__(f1) == 4, "");
_Static_assert(__alignof__(*pf) == 4, "");
_Static_assert(sizeof(f2) == 8, "");
_Static_assert(sizeof(struct M) == 12, "");

// in other positions of a declaration without declarator, both ignore them
__attribute__((aligned(16))) struct D1;
struct D1
{
  char c;
};
struct D2 __attribute__((aligned(16)));
struct D2
{
  char c;
};
_Static_assert(_Alignof(struct D1) == 1, "");
_Static_assert(_Alignof(struct D2) == 1, "");

int main()
{
  return 0;
}

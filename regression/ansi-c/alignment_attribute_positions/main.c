// The position of a packed or aligned attribute in a declaration determines
// whether it applies to a struct/union type or to the declared entity:
// between the struct/union keyword and the opening brace, and directly after
// the closing brace, it applies to the type being defined; in any other
// position, it applies to the declared object, member, or typedef. See
// attributes_declaration_without_body for those between the keyword and the
// tag of a declaration without body.

struct F
{
  char c;
  int i;
};

// aligned
__attribute__((aligned(16))) struct A1
{
  char c;
} a1;
_Static_assert(__alignof__(a1) == 16, "");
_Static_assert(_Alignof(struct A1) == 1, "");

__attribute__((aligned(16))) struct A2
{
  char c;
};
_Static_assert(_Alignof(struct A2) == 1, "");

__attribute__((aligned(16))) struct F a3;
_Static_assert(__alignof__(a3) == 16, "");

struct __attribute__((aligned(16))) F *a4;
_Static_assert(__alignof__(a4) == sizeof(void *), "");
_Static_assert(__alignof__(*a4) == 4, "");

struct F __attribute__((aligned(16))) a5;
_Static_assert(__alignof__(a5) == 16, "");

const __attribute__((aligned(16))) struct F a6;
_Static_assert(__alignof__(a6) == 16, "");

typedef __attribute__((aligned(16))) struct A7
{
  char c;
} T7;
_Static_assert(_Alignof(T7) == 16, "");
_Static_assert(_Alignof(struct A7) == 1, "");

struct A8
{
  char c;
  __attribute__((aligned(16))) struct A8i
  {
    char c;
  } m;
};
_Static_assert(sizeof(struct A8) == 32, "");
_Static_assert(_Alignof(struct A8i) == 1, "");

struct __attribute__((aligned(16))) A9
{
  char c;
} a9;
_Static_assert(__alignof__(a9) == 16, "");
_Static_assert(_Alignof(struct A9) == 16, "");

struct A10
{
  char c;
} __attribute__((aligned(16))) a10;
_Static_assert(_Alignof(struct A10) == 16, "");

struct A11
{
  char c;
} a11 __attribute__((aligned(16)));
_Static_assert(__alignof__(a11) == 16, "");
_Static_assert(_Alignof(struct A11) == 1, "");

struct F __attribute__((aligned(16))) * a12;
_Static_assert(__alignof__(a12) == 16, "");

static __attribute__((aligned(16))) struct F a13;
_Static_assert(__alignof__(a13) == 16, "");

typedef struct F __attribute__((aligned(16))) T14;
_Static_assert(_Alignof(T14) == 16, "");

struct A15
{
  char c;
} const __attribute__((aligned(16))) a15;
_Static_assert(__alignof__(a15) == 16, "");
_Static_assert(_Alignof(struct A15) == 1, "");

struct A16
{
  char c;
};
typedef __attribute__((aligned(16))) struct A16 T16;
struct A16o
{
  char c;
  T16 m;
};
_Static_assert(_Alignof(T16) == 16, "");
_Static_assert(sizeof(struct A16o) == 32, "");

struct A17
{
  char c;
  struct __attribute__((aligned(16))) F *p;
};
_Static_assert(sizeof(struct A17) == 2 * sizeof(void *), "");

// packed
__attribute__((packed)) struct P1
{
  char c;
  int i;
} p1;
_Static_assert(sizeof(p1) == 8, "");

const __attribute__((packed)) struct P2
{
  char c;
  int i;
} p2;
_Static_assert(sizeof(p2) == 8, "");

struct P3
{
  char c;
  int i;
} const __attribute__((packed)) p3;
_Static_assert(sizeof(p3) == 8, "");
_Static_assert(__alignof__(p3) == 4, "");

struct __attribute__((packed)) F p4;
_Static_assert(sizeof(p4) == 8, "");

struct P5
{
  char a;
  __attribute__((packed)) struct F m;
};
_Static_assert(sizeof(struct P5) == 9, "");

struct P6
{
  char a;
  struct F __attribute__((packed)) m;
};
_Static_assert(sizeof(struct P6) == 9, "");

struct __attribute__((packed)) P7
{
  char c;
  int i;
};
_Static_assert(sizeof(struct P7) == 5, "");

struct P8
{
  char c;
  int i;
} __attribute__((packed));
_Static_assert(sizeof(struct P8) == 5, "");

// GCC and Clang ignore a packed attribute of a typedef of a type that is not
// defined in the same declaration
typedef int TI __attribute__((packed));
struct P9
{
  char c;
  TI i;
};
_Static_assert(sizeof(struct P9) == 8, "");

typedef struct F __attribute__((packed)) TF;
struct P10
{
  char c;
  TF f;
};
_Static_assert(sizeof(struct P10) == 12, "");

// several alignment attributes of a declaration: the largest one applies
struct R1
{
  char c;
  int m __attribute__((aligned(16))) __attribute__((aligned(4)));
};
_Static_assert(sizeof(struct R1) == 32, "");

int r2 __attribute__((aligned(16))) __attribute__((aligned(4)));
_Static_assert(__alignof__(r2) == 16, "");

// several alignment attributes of a type: GCC uses the last one, Clang the
// largest one
struct __attribute__((aligned(16), aligned(4))) R3
{
  char c;
};
struct __attribute__((aligned(4))) __attribute__((aligned(16))) R4
{
  char c;
};
struct R5
{
  char c;
} __attribute__((aligned(16))) __attribute__((aligned(4)));
_Static_assert(_Alignof(struct R4) == 16, "");
#ifdef __clang__
_Static_assert(_Alignof(struct R3) == 16, "");
_Static_assert(_Alignof(struct R5) == 16, "");
#else
_Static_assert(_Alignof(struct R3) == 4, "");
_Static_assert(_Alignof(struct R5) == 4, "");
#endif

int main()
{
  return 0;
}

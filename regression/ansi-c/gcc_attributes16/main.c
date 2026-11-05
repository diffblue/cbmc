#include <stdint.h>

struct S1
{
  uint8_t c;
  int32_t i;
} __attribute__((packed));
struct S1 s1;

struct S1a
{
  uint8_t c;
  int32_t i;
} __attribute__((packed)) __attribute__((aligned(16)));
struct S1a s1a;

struct __attribute__((packed)) S2
{
  uint8_t c;
  int32_t i;
};
struct S2 s2;

struct __attribute__((packed)) __attribute__((aligned(16))) S2a
{
  uint8_t c;
  int32_t i;
};
struct S2a s2a;

// "packed" will be ignored
__attribute__((packed)) struct S3
{
  uint8_t c;
  int32_t i;
};
struct S3 s3;

// both "packed" and "aligned"
__attribute__((packed)) __attribute__((aligned(16))) struct S3a
{
  uint8_t c;
  int32_t i;
};
struct S3a s3a;

struct S4
{
  uint8_t c;
  int32_t i;
} __attribute__((packed)) s4;

struct S4a
{
  uint8_t c;
  int32_t i;
} __attribute__((packed)) __attribute__((aligned(16))) s4a;

struct __attribute__((packed)) S5
{
  uint8_t c;
  int32_t i;
} s5;

struct __attribute__((packed)) __attribute__((aligned(16))) S5a
{
  uint8_t c;
  int32_t i;
} s5a;

typedef struct __attribute__((packed)) S6
{
  uint8_t c;
  int32_t i;
} s6;

typedef struct __attribute__((packed)) __attribute__((aligned(16))) S6a
{
  uint8_t c;
  int32_t i;
} s6a;

// "packed" will be ignored in the following by both GCC and Clang
struct S7
{
  uint8_t c;
  int32_t i;
} s7 __attribute__((packed));

// "packed" will be ignored in the following by both GCC and Clang
struct S7a
{
  uint8_t c;
  int32_t i;
} s7a __attribute__((packed)) __attribute__((aligned(16)));

typedef struct T1
{
  uint8_t c;
  int32_t i;
} __attribute__((packed)) T1_t;

typedef struct T1a
{
  uint8_t c;
  int32_t i;
} __attribute__((packed)) __attribute__((aligned(16))) T1a_t;

typedef struct __attribute__((packed)) T2
{
  uint8_t c;
  int32_t i;
} T2_t;

typedef struct __attribute__((packed)) __attribute__((aligned(16))) T2a
{
  uint8_t c;
  int32_t i;
} T2a_t;

// aligned() on a typedef changes the alignment without changing the size, so
// only _Alignof (not sizeof) actually verifies it
typedef int32_t aligned_int_t __attribute__((aligned(16)));

// packed and packed+aligned unions
union __attribute__((packed)) U1
{
  uint8_t c;
  int32_t i;
};
union U1 u1;

union __attribute__((packed)) __attribute__((aligned(16))) U1a
{
  uint8_t c;
  int32_t i;
};
union U1a u1a;

// a forward declaration completed with a larger alignment exercises the
// alignment-combining path when the tag is re-encountered with a body
struct __attribute__((aligned(4))) Fwd;
struct __attribute__((aligned(16))) Fwd
{
  uint8_t c;
};
struct Fwd fwd;

// a single ignored attribute combined with a real storage-class qualifier:
// the leading aligned() is accepted-and-ignored, leaving just `static`
__attribute__((aligned(16))) static struct Q
{
  uint8_t c;
  int32_t i;
} q;

// #8443 reduction: a packed-struct typedef stays packed wherever it is used
// (its packing is part of its definition), while an `aligned` attribute on an
// outer struct that uses it still takes effect and does not interfere with the
// inner packing
typedef struct __attribute__((packed)) Inner8443
{
  uint8_t c;
  int32_t i;
} Inner8443_t;

struct __attribute__((aligned(8))) Outer8443
{
  uint8_t c;
  Inner8443_t inner;
};
struct Outer8443 outer8443;

struct PlainUser8443
{
  uint8_t c;
  Inner8443_t inner;
};
struct PlainUser8443 plain_user8443;

struct U
{
  uint8_t c;
  int32_t i;
};

struct S
{
  uint8_t c;
  // attribute ignored by GCC
  struct S1 __attribute((packed)) i1;
  struct U __attribute((packed)) i2;
  uint8_t c2;
  // alignment has to be a power of 2
  // struct S2 __attribute((aligned(5))) i2_5;
  struct S2a __attribute((aligned(8))) i3;
  uint8_t c3;
  struct S3a __attribute((aligned(8))) i4;
  uint8_t c4;
  T1a_t __attribute((aligned(8))) i5;
  T1_t __attribute((aligned(8))) i6;
};

int32_t main()
{
  _Static_assert(sizeof(struct S1) == 5, "");
  _Static_assert(sizeof(s1) == 5, "");
  _Static_assert(sizeof(struct S1a) == 16, "");
  _Static_assert(sizeof(s1a) == 16, "");

  _Static_assert(sizeof(struct S2) == 5, "");
  _Static_assert(sizeof(s2) == 5, "");
  _Static_assert(sizeof(struct S2a) == 16, "");
  _Static_assert(sizeof(s2a) == 16, "");

  _Static_assert(sizeof(struct S3) == 8, "");
  _Static_assert(sizeof(s3) == 8, "");
  _Static_assert(sizeof(struct S3a) == 8, "");
  _Static_assert(sizeof(s3a) == 8, "");

  _Static_assert(sizeof(struct S4) == 5, "");
  _Static_assert(sizeof(s4) == 5, "");
  _Static_assert(sizeof(struct S4a) == 16, "");
  _Static_assert(sizeof(s4a) == 16, "");

  _Static_assert(sizeof(struct S5) == 5, "");
  _Static_assert(sizeof(s5) == 5, "");
  _Static_assert(sizeof(struct S5a) == 16, "");
  _Static_assert(sizeof(s5a) == 16, "");

  _Static_assert(sizeof(struct S6) == 5, "");
  _Static_assert(sizeof(s6) == 5, "");
  _Static_assert(sizeof(struct S6a) == 16, "");
  _Static_assert(sizeof(s6a) == 16, "");

  _Static_assert(sizeof(struct S7) == 8, "");
  _Static_assert(sizeof(s7) == 8, "");
  _Static_assert(sizeof(struct S7a) == 8, "");
  _Static_assert(sizeof(s7a) == 8, "");

  _Static_assert(sizeof(struct T1) == 5, "");
  _Static_assert(sizeof(T1_t) == 5, "");
  _Static_assert(sizeof(struct T1a) == 16, "");
  _Static_assert(sizeof(T1a_t) == 16, "");

  _Static_assert(sizeof(struct T2) == 5, "");
  _Static_assert(sizeof(T2_t) == 5, "");
  _Static_assert(sizeof(struct T2a) == 16, "");
  _Static_assert(sizeof(T2a_t) == 16, "");

  // alignment values verified directly: sizeof alone would not catch a wrong
  // alignment that doesn't change the size
  _Static_assert(_Alignof(struct S1a) == 16, "");
  _Static_assert(_Alignof(struct S2a) == 16, "");
  _Static_assert(_Alignof(aligned_int_t) == 16, "");
  _Static_assert(sizeof(aligned_int_t) == 4, "");

  _Static_assert(sizeof(union U1) == 4, "");
  _Static_assert(_Alignof(union U1) == 1, "");
  // CBMC does not add tail padding to a union to reach its alignment, so only
  // the alignment (not the size) of an aligned union is asserted here.
  _Static_assert(_Alignof(union U1a) == 16, "");

  _Static_assert(_Alignof(struct Fwd) == 16, "");

  _Static_assert(sizeof(struct Q) == 8, "");
  _Static_assert(_Alignof(struct Q) == 4, "");

  _Static_assert(sizeof(Inner8443_t) == 5, "");
  _Static_assert(_Alignof(Inner8443_t) == 1, "");
  _Static_assert(sizeof(struct Outer8443) == 8, "");
  _Static_assert(_Alignof(struct Outer8443) == 8, "");
  _Static_assert(sizeof(struct PlainUser8443) == 6, "");
  _Static_assert(_Alignof(struct PlainUser8443) == 1, "");

  _Static_assert(sizeof(struct S) == 96, "");
  return 0;
}

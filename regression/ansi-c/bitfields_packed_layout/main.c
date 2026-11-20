// Bit-fields in packed aggregates and under #pragma pack, and zero-width
// bit-fields, as laid out by GCC and Clang.

// bit-fields are densely packed in a packed aggregate
struct P1
{
  int m : 7;
} __attribute__((packed));
struct P2
{
  char c;
  int m : 7;
} __attribute__((packed));
struct P3
{
  long long m : 8;
} __attribute__((packed));
union P4
{
  long long m : 7;
} __attribute__((packed));

_Static_assert(sizeof(struct P1) == 1 && _Alignof(struct P1) == 1, "P1");
_Static_assert(sizeof(struct P2) == 2 && _Alignof(struct P2) == 1, "P2");
_Static_assert(sizeof(struct P3) == 1 && _Alignof(struct P3) == 1, "P3");
_Static_assert(sizeof(union P4) == 1 && _Alignof(union P4) == 1, "P4");

// #pragma pack(n) caps the alignment of bit-fields at n, even when packed
#pragma pack(push, 2)
union U1
{
  long long m : 7;
} __attribute__((packed));
struct S1
{
  long long m : 7;
} __attribute__((packed));
struct S2
{
  long long m : 7;
};
#pragma pack(pop)

_Static_assert(sizeof(union U1) == 2 && _Alignof(union U1) == 2, "U1");
_Static_assert(sizeof(struct S1) == 2 && _Alignof(struct S1) == 2, "S1");
_Static_assert(sizeof(struct S2) == 2 && _Alignof(struct S2) == 2, "S2");

// a zero-width bit-field aligns the next member to its underlying type, even
// when packed, but does not affect the alignment of the aggregate
#pragma pack(push, 1)
struct Z1
{
  long long m : 4;
  long long : 0;
};
struct Z2
{
  char c;
  long long : 0;
  char d;
};
#pragma pack(pop)
struct Z3
{
  long long : 0;
};
struct Z4
{
  char c;
  long long : 0;
  char d;
};
struct Z5
{
  char c;
  long long : 0;
  char d;
} __attribute__((packed));
struct Z6
{
  char c;
  int : 0;
};
struct Z7
{
  char a;
  int b : 4;
  long long : 0;
  char d;
};
union Z8
{
  int : 0;
  char c;
};

#if(defined(__arm__) || defined(__aarch64__)) && !defined(__APPLE__)
// the ARM procedure call standard also makes zero-width bit-fields affect the
// alignment of the aggregate
_Static_assert(sizeof(struct Z1) == 8 && _Alignof(struct Z1) == 8, "Z1");
_Static_assert(sizeof(struct Z2) == 16 && _Alignof(struct Z2) == 8, "Z2");
_Static_assert(sizeof(struct Z3) == 0 && _Alignof(struct Z3) == 8, "Z3");
_Static_assert(sizeof(struct Z4) == 16 && _Alignof(struct Z4) == 8, "Z4");
_Static_assert(sizeof(struct Z5) == 16 && _Alignof(struct Z5) == 8, "Z5");
_Static_assert(sizeof(struct Z6) == 4 && _Alignof(struct Z6) == 4, "Z6");
_Static_assert(sizeof(struct Z7) == 16 && _Alignof(struct Z7) == 8, "Z7");
_Static_assert(sizeof(union Z8) == 4 && _Alignof(union Z8) == 4, "Z8");
#else
_Static_assert(sizeof(struct Z1) == 8 && _Alignof(struct Z1) == 1, "Z1");
_Static_assert(sizeof(struct Z2) == 9 && _Alignof(struct Z2) == 1, "Z2");
_Static_assert(sizeof(struct Z3) == 0 && _Alignof(struct Z3) == 1, "Z3");
_Static_assert(sizeof(struct Z4) == 9 && _Alignof(struct Z4) == 1, "Z4");
_Static_assert(sizeof(struct Z5) == 9 && _Alignof(struct Z5) == 1, "Z5");
_Static_assert(sizeof(struct Z6) == 4 && _Alignof(struct Z6) == 1, "Z6");
_Static_assert(sizeof(struct Z7) == 12 && _Alignof(struct Z7) == 4, "Z7");
_Static_assert(sizeof(union Z8) == 1 && _Alignof(union Z8) == 1, "Z8");
#endif

int main()
{
  return 0;
}

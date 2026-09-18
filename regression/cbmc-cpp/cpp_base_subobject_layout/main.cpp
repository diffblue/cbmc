extern "C" void __CPROVER_assert(bool, const char *);
// Itanium C++ ABI 2.4 base-subobject layout (g++/clang on x86-64): a base
// subobject is placed at the next offset aligned for the base; a base that is
// a POD for the purpose of layout keeps its tail padding, the members of the
// derived class start after sizeof(Base); for a non-POD base they may start in
// its tail padding (dsize < sizeof).  Empty bases take no space.
struct B1 { long l; short s; };            // POD: size 16, 6 bytes tail padding
struct D1 : B1 { char c; };
struct D2 : B1 { bool b : 1; int i; };
struct B2 { long l; short s; B2() : l(0), s(0) {} }; // non-POD: dsize 10
struct D3 : B2 { char c; };
struct D4 : B2 { bool b : 1; int i; };
struct B3 { int i : 29; };
struct D5 : B3 { int j : 3; };
struct B4 { int i : 29; B4() : i(0) {} };
struct D6 : B4 { int j : 3; };
struct B5 { char c; };
struct B7 { char c; int i; };
struct M1 : B5, B7 { char z; };            // B7 subobject aligned to 4
struct M2 : B2, B5 { };                   // B5 at dsize(B2) = 10
struct EB {};
struct D7 : EB, B1 { char c; };           // empty base takes no space
struct D8 : B1 { int m : 28; short s2; };
struct P1 { char c; int i; } __attribute__((packed));            // packed POD base: 5
struct PD1 : public P1 { int m; };                                // m at 8
struct P2 { char c; union { long a; double b; }; } __attribute__((packed)); // 9
struct PD2 : public P2 { int m; };                                // m at 12
struct P3 { char c; long l; } __attribute__((packed));            // 9
struct PD3 : public P3 { int m; };                                // l stays at 1, m at 12
struct alignas(32) A3 { short m4 : 13; float m7; };
struct A11 : public A3 { A3 m12; unsigned long m13; short m15; } __attribute__((packed, aligned(8)));
struct A2 : public A3 { char c; };
struct A4 : public A3 { char c; } __attribute__((packed));
int main()
{
  __CPROVER_assert(sizeof(D1) == 24 && __builtin_offsetof(D1, c) == 16, "POD base keeps its tail padding");
  __CPROVER_assert(sizeof(D2) == 24 && __builtin_offsetof(D2, i) == 20, "bit-field after a POD base");
  __CPROVER_assert(sizeof(D3) == 16 && __builtin_offsetof(D3, c) == 10, "non-POD base: member in its tail padding");
  __CPROVER_assert(sizeof(D4) == 16 && __builtin_offsetof(D4, i) == 12, "bit-field then int in the tail padding");
  __CPROVER_assert(sizeof(D5) == 8, "bit-field after a POD bit-field base");
  __CPROVER_assert(sizeof(D6) == 8, "bit-field after a non-POD bit-field base: next byte");
  __CPROVER_assert(sizeof(M1) == 16 && __builtin_offsetof(M1, i) == 8 && __builtin_offsetof(M1, z) == 12, "second base subobject aligned for the base");
  __CPROVER_assert(sizeof(M2) == 16, "second (POD) base placed at dsize of a non-POD first base");
  __CPROVER_assert(sizeof(D7) == 24 && __builtin_offsetof(D7, c) == 16, "empty base");
  __CPROVER_assert(sizeof(D8) == 24 && __builtin_offsetof(D8, s2) == 20, "bit-field run then short after a POD base");
  __CPROVER_assert(alignof(A11) == 32 && sizeof(A11) == 96 && __builtin_offsetof(A11, m12) == 32 && __builtin_offsetof(A11, m15) == 72, "packed derived class keeps the base alignment (alignas(32) base)");
  __CPROVER_assert(alignof(A2) == 32 && sizeof(A2) == 64 && alignof(A4) == 32 && sizeof(A4) == 64, "derived (also packed) of an over-aligned base");
  __CPROVER_assert(sizeof(PD1) == 12 && __builtin_offsetof(PD1, m) == 8, "derived from a packed base");
  __CPROVER_assert(sizeof(PD2) == 16 && __builtin_offsetof(PD2, m) == 12, "packed base with an anonymous union");
  __CPROVER_assert(sizeof(PD3) == 16 && __builtin_offsetof(PD3, m) == 12 && __builtin_offsetof(PD3, l) == 1, "the packed base's members keep their packed offsets");
  D3 d3; d3.l = 1; d3.s = 2; d3.c = 3;
  D4 d4; d4.b = 1; d4.i = 5;
  __CPROVER_assert(d3.l == 1 && d3.s == 2 && d3.c == 3 && d4.b && d4.i == 5 && d4.l == 0, "members accessible");
  return 0;
}

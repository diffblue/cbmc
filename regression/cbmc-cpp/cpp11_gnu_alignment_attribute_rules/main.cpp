extern "C" void __CPROVER_assert(bool, const char *);
#include <cstddef>
#include <cstdint>
// GCC alignment rules (values: g++ 13 / clang++ 18, x86-64):
// aligned(n) on a member/struct can only increase; as part of a typedef it
// sets the alignment exactly; in an alias-declaration g++ ignores it on a
// class type; a packed struct's members are byte-aligned unless they carry
// their own aligned(n); an unnamed bit-field never raises the alignment.
typedef uint32_t __attribute__((aligned(1))) unaligned_u32;
struct S { int a; int b; };
typedef S __attribute__((aligned(16))) S16;
using S16u = S __attribute__((aligned(16)));
struct M { char c; int x __attribute__((aligned(2))); };
struct N { char c; unaligned_u32 u; };
struct Q { char c; S16 s; };
struct R { int a; } __attribute__((aligned(2)));
struct P2 { char c; int x __attribute__((aligned(4))); } __attribute__((packed));
struct P1 { char c; S16 s; } __attribute__((packed));
struct A1 { char c; int : 0; char d; };
struct A2 { char c; int : 3; char d; };
// two attributes in one group on a member declarator: the base type must
// survive (`long' was turned into `int')
struct G { long m __attribute__((packed, aligned(2))); unsigned char b : 8; } __attribute__((packed, aligned(2)));
int main()
{
  __CPROVER_assert(alignof(unaligned_u32) == 1, "typedef aligned(1) decreases");
  __CPROVER_assert(sizeof(S16) == 8 && alignof(S16) == 16, "typedef aligned(16) of a class");
  __CPROVER_assert(sizeof(S16u) == 8 && alignof(S16u) == 4, "alias-declaration: attribute on a class type ignored");
  __CPROVER_assert(sizeof(M) == 8 && offsetof(M, x) == 4, "member aligned(2) cannot decrease");
  __CPROVER_assert(sizeof(N) == 5 && offsetof(N, u) == 1, "member of unaligned typedef");
  __CPROVER_assert(sizeof(Q) == 32 && offsetof(Q, s) == 16, "member of aligned(16) typedef'd class");
  __CPROVER_assert(sizeof(R) == 4 && alignof(R) == 4, "struct aligned(2) cannot decrease");
  __CPROVER_assert(sizeof(P2) == 8 && alignof(P2) == 4 && offsetof(P2, x) == 4, "packed struct, member with its own aligned(4)");
  __CPROVER_assert(sizeof(P1) == 9 && alignof(P1) == 1 && offsetof(P1, s) == 1, "packed struct ignores the member type's alignment");
  __CPROVER_assert(sizeof(A1) == 5 && alignof(A1) == 1 && offsetof(A1, d) == 4, "unnamed zero-width bit-field: aligns, occupies, no alignment");
  __CPROVER_assert(sizeof(A2) == 3 && alignof(A2) == 1 && offsetof(A2, d) == 2, "unnamed bit-field occupies its bits");
  __CPROVER_assert(sizeof(G) == 10 && alignof(G) == 2, "attribute group on a long member");
  G g{}; g.m = 0x7fffffffffL; g.b = 200;
  __CPROVER_assert(g.m == 0x7fffffffffL && g.b == 200, "values");
  return 0;
}

extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [dcl.align]: alignas in the decl-specifier-seq of a member whose type
// is a typedef-name was lost by the parser (kept only for built-in types);
// /5: it cannot weaken the alignment the typedef-name itself carries.
typedef unsigned short __attribute__((aligned(1))) T7;
typedef unsigned short __attribute__((aligned(8))) T8;
struct S1 { char c; alignas(32) T7 m; };
struct S3 { char c; T7 m; };
struct S4 { char c; T7 m __attribute__((aligned(4))); };
struct S5 { char c; __attribute__((aligned(32))) T7 m; };
struct S6 { char c; alignas(16) unsigned short m; };
struct alignas(32) C32 { int i; };
typedef C32 __attribute__((aligned(16))) T22;
struct S7 { unsigned m24; T22 m25 __attribute__((aligned(4))); };
struct S8 { unsigned m24; T22 m25 __attribute__((aligned(64))); };
typedef unsigned char __attribute__((aligned(8))) T8c;
struct S9 { char c; T8c x __attribute__((aligned(4))); } __attribute__((packed));
int main()
{
  __CPROVER_assert(sizeof(S1) == 64 && alignof(S1) == 32 && __builtin_offsetof(S1, m) == 32, "S1 alignas(32) on an aligned(1) typedef");
  __CPROVER_assert(sizeof(S3) == 3 && alignof(S3) == 1 && __builtin_offsetof(S3, m) == 1, "S3 aligned(1) typedef");
  __CPROVER_assert(sizeof(S4) == 8 && alignof(S4) == 4 && __builtin_offsetof(S4, m) == 4, "S4 aligned(4) attribute on an aligned(1) typedef member");
  __CPROVER_assert(alignof(S5) == 32 && __builtin_offsetof(S5, m) == 32, "S5 leading GCC attribute on a typedef-name member");
  __CPROVER_assert(alignof(S6) == 16 && sizeof(S6) == 32, "S6 built-in type");
  __CPROVER_assert(alignof(T22) == 16 && alignof(S7) == 16 && __builtin_offsetof(S7, m25) == 16, "S7 trailing aligned(4) does not lower the typedef's 16");
  __CPROVER_assert(alignof(S8) == 64 && __builtin_offsetof(S8, m25) == 64, "S8 trailing aligned(64) raises");
  __CPROVER_assert(__builtin_offsetof(S9, x) == 4 && sizeof(S9) == 8, "S9 packed: the member's own aligned(4) counts, the typedef's 8 does not");
  return 0;
}

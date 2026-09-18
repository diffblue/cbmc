extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [dcl.align]/1: an alignment-specifier in the decl-specifier-seq
// appertains to the declared object -- for `alignas(16) void *p;' the POINTER
// (it was attached to the pointee type and ignored by the layout).
struct S9 { long m5[3]; alignas(16) void *m8; };
struct S10 { char c; __attribute__((aligned(16))) int *p; };
struct S11 { char c; int *p __attribute__((aligned(16))); };
struct S12 { char c; alignas(16) int &r; S12(int &x) : r(x) {} };
#pragma pack(push, 2)
struct S13 { char c; alignas(16) void *p; };
#pragma pack(pop)
int main()
{
  __CPROVER_assert(__builtin_offsetof(S9, m8) == 32 && sizeof(S9) == 48 && alignof(S9) == 16, "alignas(16) void *m: the pointer is aligned");
  __CPROVER_assert(__builtin_offsetof(S10, p) == 16 && sizeof(S10) == 32, "leading GCC attribute");
  __CPROVER_assert(__builtin_offsetof(S11, p) == 16 && sizeof(S11) == 32, "trailing GCC attribute");
  __CPROVER_assert(sizeof(S12) == 32 && alignof(S12) == 16, "reference member");
  __CPROVER_assert(__builtin_offsetof(S13, p) == 2 && sizeof(S13) == 10 && alignof(S13) == 2, "pack(2) caps the pointer's alignas(16)");
  int v = 3; S12 s(v); s.r = 4;
  __CPROVER_assert(v == 4, "reference member works");
  return 0;
}

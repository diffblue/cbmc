// Under #pragma pack(n), a member's alignment is capped at the smaller of n
// and the member's natural alignment. This must also hold when the member is
// an array (the cap applies to the element type) and when a wider field forces
// a larger natural alignment that packing then reduces. Regression for an
// over-alignment that inflated struct sizes (observed via the Xen compat-ABI
// CHECK_ size assertions, e.g. CHECK_vcpu_hvm_context).

// A short array after an odd number of shorts: with pack(4) the array keeps
// alignment min(4, 2) = 2, so it stays at the next even (not multiple-of-4)
// offset. Over-aligning it to 4 would push it to offset 12 and inflate the
// size.
#pragma pack(4)
struct S
{
  unsigned short head[5]; // 10 bytes at offset 0
  unsigned short tail[3]; // alignment 2, hence offset 10
};
#pragma pack()

_Static_assert(__builtin_offsetof(struct S, tail) == 10, "tail at offset 10");
_Static_assert(sizeof(struct S) == 16, "size 16");
_Static_assert(_Alignof(struct S) == 2, "alignment 2");

// A 64-bit field under pack(4) is capped to alignment 4, and a trailing
// short array remains 2-aligned (mirrors the vcpu_hvm_x86_32 layout).
#pragma pack(4)
struct T
{
  unsigned a[14];        // 56 bytes
  unsigned long long w;  // alignment min(4, 8) = 4, offset 56
  unsigned b[10];        // offset 64
  unsigned short c[5];   // offset 104
  unsigned short pad[3]; // alignment 2, offset 114
};
#pragma pack()

_Static_assert(__builtin_offsetof(struct T, w) == 56, "w at 56");
_Static_assert(__builtin_offsetof(struct T, pad) == 114, "pad at 114");
_Static_assert(sizeof(struct T) == 120, "size 120");
_Static_assert(_Alignof(struct T) == 4, "alignment 4");

int main()
{
  return 0;
}

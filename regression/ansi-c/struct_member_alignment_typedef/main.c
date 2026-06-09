// KNOWNBUG: a typedef that *reduces* alignment via __attribute__((aligned(n)))
// keeps that reduced alignment when used as a struct member. GCC, Clang and
// Intel icx all honour it (verified on Compiler Explorer) -- the member (and
// hence the enclosing struct) is aligned to n, so for the struct below they
// all report alignment 2, size 6, and offsetof(x) == 2.
//
// CBMC currently over-aligns such a member to the type's natural alignment.
// The front-end stores a type-level alignment attribute (from the typedef)
// identically to a member-declarator alignment attribute, and the latter may
// only *increase* a member's alignment per GCC/Clang (a smaller request is
// ignored -- see the M_a2 case in struct_member_alignment, which CBMC handles
// correctly). The two are indistinguishable in the IR, so honouring the
// type-level reduction would wrongly also honour the declarator-level one.
// Distinguishing them requires tracking the provenance of the alignment
// attribute, which CBMC does not currently do.
//
// Promote this test to CORE once alignment provenance is tracked.

typedef int __attribute__((aligned(2))) ai2_t;

// The typedef on its own is handled correctly (alignment 2).
_Static_assert(_Alignof(ai2_t) == 2, "typedef alignment is 2");

struct M
{
  char c;
  ai2_t x;
};

// GCC/Clang: the member keeps the typedef's reduced alignment of 2, so x is at
// offset 2 and the struct is 6 bytes with alignment 2. CBMC currently computes
// alignment 4 (x at offset 4, size 8).
_Static_assert(_Alignof(struct M) == 2, "member keeps reduced alignment");
_Static_assert(__builtin_offsetof(struct M, x) == 2, "x at offset 2");
_Static_assert(sizeof(struct M) == 6, "no over-alignment padding");

int main(void)
{
  return 0;
}

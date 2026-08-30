// A typedef that *reduces* alignment via __attribute__((aligned(n))) keeps that
// reduced alignment when used as a struct member: the member (and hence the
// enclosing struct) is aligned to n. This matches GCC, Clang and Intel icx
// (verified on Compiler Explorer).
//
// This is distinct from an alignment attribute on the member's *declarator*,
// which can only increase the alignment (a smaller request is ignored -- see
// the M_a2 case in struct_member_alignment). The two are told apart by the
// C_alignment_increase_only provenance flag, set when the attribute comes from
// an object/field/tag declaration rather than a typedef.

typedef int __attribute__((aligned(2))) ai2_t;

// The typedef on its own has alignment 2.
_Static_assert(_Alignof(ai2_t) == 2, "typedef alignment is 2");

struct M
{
  char c;
  ai2_t x;
};

// The member keeps the typedef's reduced alignment of 2: x is at offset 2 and
// the struct is 6 bytes with alignment 2.
_Static_assert(_Alignof(struct M) == 2, "member keeps reduced alignment");
_Static_assert(__builtin_offsetof(struct M, x) == 2, "x at offset 2");
_Static_assert(sizeof(struct M) == 6, "no over-alignment padding");

// A reducing alignment on the member declarator (not the type) is ignored,
// exactly as GCC/Clang do; the member stays at the natural alignment of 4.
struct N
{
  char c;
  int y __attribute__((aligned(2)));
};

_Static_assert(_Alignof(struct N) == 4, "declarator reduce is ignored");

int main(void)
{
  return 0;
}

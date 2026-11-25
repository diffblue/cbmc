// System V psABI (AMD64 and i386), section 3.1.2, Bit-Fields: "Unnamed
// bit-fields' types do not affect the alignment of a structure or union."
// GCC and Clang follow this rule on all targets other than those using the
// Microsoft ABI or AAPCS (Arm, other than on Apple platforms).

struct unnamed_bits
{
  unsigned int : 1;
  char tag;
};

struct separator
{
  char first;
  unsigned int : 0;
  char last;
};

struct named_bits
{
  unsigned int value : 1;
  char tag;
};

union unnamed_union
{
  unsigned int : 1;
  char tag;
};

struct nested
{
  char first;
  struct unnamed_bits member;
  char last;
};

struct trailing
{
  char c;
  int : 4;
};

struct wide
{
  char a;
  long long : 3;
  char b;
};

_Static_assert(sizeof(struct unnamed_bits) == 2, "sizeof(struct unnamed_bits)");
_Static_assert(
  _Alignof(struct unnamed_bits) == 1,
  "_Alignof(struct unnamed_bits)");
_Static_assert(
  __builtin_offsetof(struct unnamed_bits, tag) == 1,
  "offsetof(struct unnamed_bits, tag)");
_Static_assert(sizeof(struct separator) == 5, "sizeof(struct separator)");
_Static_assert(_Alignof(struct separator) == 1, "_Alignof(struct separator)");
_Static_assert(
  __builtin_offsetof(struct separator, last) == 4,
  "offsetof(struct separator, last)");
_Static_assert(sizeof(struct named_bits) == 4, "sizeof(struct named_bits)");
_Static_assert(_Alignof(struct named_bits) == 4, "_Alignof(struct named_bits)");
_Static_assert(sizeof(union unnamed_union) == 1, "sizeof(union unnamed_union)");
_Static_assert(
  _Alignof(union unnamed_union) == 1,
  "_Alignof(union unnamed_union)");
_Static_assert(sizeof(struct nested) == 4, "sizeof(struct nested)");
_Static_assert(_Alignof(struct nested) == 1, "_Alignof(struct nested)");
_Static_assert(
  __builtin_offsetof(struct nested, member) == 1,
  "offsetof(struct nested, member)");
_Static_assert(sizeof(struct trailing) == 2, "sizeof(struct trailing)");
_Static_assert(_Alignof(struct trailing) == 1, "_Alignof(struct trailing)");
_Static_assert(sizeof(struct wide) == 3, "sizeof(struct wide)");
_Static_assert(_Alignof(struct wide) == 1, "_Alignof(struct wide)");
_Static_assert(
  __builtin_offsetof(struct wide, b) == 2,
  "offsetof(struct wide, b)");

int main(void)
{
  return 0;
}

// With AAPCS and AAPCS64 (Arm, other than on Apple platforms), unnamed
// bit-fields do affect the alignment of a structure or union.

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

_Static_assert(sizeof(struct unnamed_bits) == 4, "sizeof(struct unnamed_bits)");
_Static_assert(
  _Alignof(struct unnamed_bits) == 4,
  "_Alignof(struct unnamed_bits)");
_Static_assert(
  __builtin_offsetof(struct unnamed_bits, tag) == 1,
  "offsetof(struct unnamed_bits, tag)");
_Static_assert(sizeof(struct separator) == 8, "sizeof(struct separator)");
_Static_assert(_Alignof(struct separator) == 4, "_Alignof(struct separator)");
_Static_assert(
  __builtin_offsetof(struct separator, last) == 4,
  "offsetof(struct separator, last)");
_Static_assert(sizeof(struct named_bits) == 4, "sizeof(struct named_bits)");
_Static_assert(_Alignof(struct named_bits) == 4, "_Alignof(struct named_bits)");
_Static_assert(sizeof(union unnamed_union) == 4, "sizeof(union unnamed_union)");
_Static_assert(
  _Alignof(union unnamed_union) == 4,
  "_Alignof(union unnamed_union)");
_Static_assert(sizeof(struct nested) == 12, "sizeof(struct nested)");
_Static_assert(_Alignof(struct nested) == 4, "_Alignof(struct nested)");
_Static_assert(
  __builtin_offsetof(struct nested, member) == 4,
  "offsetof(struct nested, member)");
_Static_assert(sizeof(struct trailing) == 4, "sizeof(struct trailing)");
_Static_assert(_Alignof(struct trailing) == 4, "_Alignof(struct trailing)");
_Static_assert(sizeof(struct wide) == 8, "sizeof(struct wide)");
_Static_assert(_Alignof(struct wide) == 8, "_Alignof(struct wide)");
_Static_assert(
  __builtin_offsetof(struct wide, b) == 2,
  "offsetof(struct wide, b)");

int main(void)
{
  return 0;
}

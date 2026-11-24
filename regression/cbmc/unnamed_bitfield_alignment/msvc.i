// With the Microsoft ABI, unnamed bit-fields do affect the alignment of a
// structure. CBMC does not yet implement the Microsoft layout of zero-width
// bit-fields, nor the alignment of unions with unnamed bit-fields (which is not
// affected by those), so those are not checked here.

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

_Static_assert(sizeof(struct unnamed_bits) == 8, "sizeof(struct unnamed_bits)");
_Static_assert(
  _Alignof(struct unnamed_bits) == 4,
  "_Alignof(struct unnamed_bits)");
_Static_assert(sizeof(struct named_bits) == 8, "sizeof(struct named_bits)");
_Static_assert(_Alignof(struct named_bits) == 4, "_Alignof(struct named_bits)");
_Static_assert(sizeof(union unnamed_union) == 4, "sizeof(union unnamed_union)");
_Static_assert(sizeof(struct nested) == 16, "sizeof(struct nested)");
_Static_assert(_Alignof(struct nested) == 4, "_Alignof(struct nested)");
_Static_assert(sizeof(struct trailing) == 8, "sizeof(struct trailing)");
_Static_assert(_Alignof(struct trailing) == 4, "_Alignof(struct trailing)");
_Static_assert(sizeof(struct wide) == 24, "sizeof(struct wide)");
_Static_assert(_Alignof(struct wide) == 8, "_Alignof(struct wide)");

int main(void)
{
  return 0;
}

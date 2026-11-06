#include <assert.h>
#include <stddef.h>

// System V x86-64 psABI, 3.1.2 (Bit-Fields): "Unnamed bit-fields' types do not
// affect the alignment of a structure or union."
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

int main(void)
{
// CBMC only applies this rule to x86-64 Linux. The host's predefined macros
// stay visible when --arch selects another target, hence the extra check.
#if defined(__x86_64__) && defined(__LP64__) && defined(__linux__) &&          \
  !defined(__aarch64__)
  assert(sizeof(struct unnamed_bits) == 2);
  assert(_Alignof(struct unnamed_bits) == 1);
  assert(offsetof(struct unnamed_bits, tag) == 1);

  // The separator still aligns the following member to its underlying type.
  assert(sizeof(struct separator) == 5);
  assert(_Alignof(struct separator) == 1);
  assert(offsetof(struct separator, last) == 4);

  assert(sizeof(struct named_bits) == 4);
  assert(_Alignof(struct named_bits) == 4);

  assert(sizeof(union unnamed_union) == 1);
  assert(_Alignof(union unnamed_union) == 1);

  assert(sizeof(struct nested) == 4);
  assert(_Alignof(struct nested) == 1);
  assert(offsetof(struct nested, member) == 1);
#endif
}

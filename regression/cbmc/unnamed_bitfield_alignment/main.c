#include <assert.h>
#include <stddef.h>

// System V AMD64: unnamed bit-fields do not affect aggregate alignment.
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
}

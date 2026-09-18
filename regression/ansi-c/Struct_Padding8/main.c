// System V ABI / GCC: a bit-field must be contained in a storage unit of its
// declared type (the type-sized slots counted from the start of the struct);
// one that does not fit in what remains of the current unit starts at the
// next one.  The struct is not laid out as a dense bit stream: `A1' is 3
// bytes, not 2.  A packed struct does pack densely.
#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__
#include <stddef.h>
#include <stdint.h>

struct A1
{
  uint8_t a : 6;
  uint8_t r : 1;
  uint8_t b : 4;
  uint8_t c : 5;
};
STATIC_ASSERT(sizeof(struct A1) == 3);

struct A1p
{
  uint8_t a : 6;
  uint8_t r : 1;
  uint8_t b : 4;
  uint8_t c : 5;
} __attribute__((packed));
STATIC_ASSERT(sizeof(struct A1p) == 2);

struct B1
{
  char a;
  int b : 31;
};
STATIC_ASSERT(sizeof(struct B1) == 8);

struct B3
{
  uint16_t a : 12;
  uint8_t b : 5;
  uint8_t c : 3;
};
STATIC_ASSERT(sizeof(struct B3) == 4);

struct B4
{
  uint8_t a : 5;
  uint16_t b : 12;
  uint8_t c : 4;
};
STATIC_ASSERT(sizeof(struct B4) == 4);

struct B5
{
  uint32_t a : 20;
  uint8_t b : 7;
  uint8_t c : 7;
  uint32_t d : 10;
};
STATIC_ASSERT(sizeof(struct B5) == 8);

struct B6
{
  uint8_t a : 7;
  uint32_t b : 30;
  uint8_t c : 3;
};
STATIC_ASSERT(sizeof(struct B6) == 12);

// a plain member after a run whose end moved because of unit padding
struct B7
{
  uint8_t a : 6;
  uint8_t r : 1;
  uint8_t b : 4;
  uint8_t c : 5;
  uint8_t d;
};
STATIC_ASSERT(sizeof(struct B7) == 4);
STATIC_ASSERT(offsetof(struct B7, d) == 3);
#endif

int main()
{
  return 0;
}

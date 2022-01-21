#include <assert.h>
#include <stdint.h>

#define test_bit_reverse(W)                                                    \
  uint##W##_t test_bit_reverse##W(uint##W##_t v)                               \
  {                                                                            \
    uint##W##_t result = 0;                                                    \
    int i;                                                                     \
    for(i = 0; i < W; i++)                                                     \
    {                                                                          \
      if(v & (1ULL << i))                                                      \
        result |= 1ULL << (W - i - 1);                                         \
    }                                                                          \
    return result;                                                             \
  }                                                                            \
  int dummy_for_semicolon##W

test_bit_reverse(8);
test_bit_reverse(16);
test_bit_reverse(32);
test_bit_reverse(64);

#ifndef __clang__
unsigned char __builtin_bitreverse8(unsigned char);
unsigned short __builtin_bitreverse16(unsigned short);
unsigned int __builtin_bitreverse32(unsigned int);
unsigned long long __builtin_bitreverse64(unsigned long long);
#endif

void check_8(void)
{
  uint8_t op;
  assert(__builtin_bitreverse8(op) == test_bit_reverse8(op));
  assert(__builtin_bitreverse8(1) == 0x80);
}

void check_16(void)
{
  uint16_t op;
  assert(__builtin_bitreverse16(op) == test_bit_reverse16(op));
  assert(__builtin_bitreverse16(1) == 0x8000);
}

void check_32(void)
{
  uint32_t op;
  assert(__builtin_bitreverse32(op) == test_bit_reverse32(op));
  assert(__builtin_bitreverse32(1) == 0x80000000);
}

void check_64(void)
{
  uint64_t op;
  assert(__builtin_bitreverse64(op) == test_bit_reverse64(op));
  assert(__builtin_bitreverse64(1) == 0x8000000000000000ULL);
}

int main(void)
{
  check_8();
  check_16();
  check_32();
  check_64();
}

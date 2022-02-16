#include <assert.h>
#include <limits.h>
#include <stdint.h>

#define rol(type, x, d)                                                        \
  ((type)(((x) << (d)) | ((x) >> ((8 * sizeof(type)) - (d)))))

#define ror(type, x, d)                                                        \
  ((type)(((x) >> (d)) | ((x) << ((8 * sizeof(type)) - (d)))))

#ifndef __clang__
unsigned char __builtin_rotateleft8(unsigned char, unsigned char);
unsigned short __builtin_rotateleft16(unsigned short, unsigned short);
unsigned int __builtin_rotateleft32(unsigned int, unsigned int);
unsigned long long
__builtin_rotateleft64(unsigned long long, unsigned long long);

unsigned char __builtin_rotateright8(unsigned char, unsigned char);
unsigned short __builtin_rotateright16(unsigned short, unsigned short);
unsigned int __builtin_rotateright32(unsigned int, unsigned int);
unsigned long long
__builtin_rotateright64(unsigned long long, unsigned long long);
#endif

void check_left8(void)
{
  uint8_t op;
  assert(__builtin_rotateleft8(op, 1) == rol(uint8_t, op, 1));
  assert(__builtin_rotateleft8(op, 2) == rol(uint8_t, op, 2));
  assert(__builtin_rotateleft8(op, 3) == rol(uint8_t, op, 3));
  assert(__builtin_rotateleft8(op, 4) == rol(uint8_t, op, 4));
}

void check_left16(void)
{
  uint16_t op;
  assert(__builtin_rotateleft16(op, 1) == rol(uint16_t, op, 1));
  assert(__builtin_rotateleft16(op, 2) == rol(uint16_t, op, 2));
  assert(__builtin_rotateleft16(op, 3) == rol(uint16_t, op, 3));
  assert(__builtin_rotateleft16(op, 4) == rol(uint16_t, op, 4));
}

void check_left32(void)
{
  uint32_t op;
  assert(__builtin_rotateleft32(op, 1) == rol(uint32_t, op, 1));
  assert(__builtin_rotateleft32(op, 2) == rol(uint32_t, op, 2));
  assert(__builtin_rotateleft32(op, 3) == rol(uint32_t, op, 3));
  assert(__builtin_rotateleft32(op, 4) == rol(uint32_t, op, 4));
}

void check_left64(void)
{
  uint64_t op;
  assert(__builtin_rotateleft64(op, 1) == rol(uint64_t, op, 1));
  assert(__builtin_rotateleft64(op, 2) == rol(uint64_t, op, 2));
  assert(__builtin_rotateleft64(op, 3) == rol(uint64_t, op, 3));
  assert(__builtin_rotateleft64(op, 4) == rol(uint64_t, op, 4));
}

void check_right8(void)
{
  uint8_t op;
  assert(__builtin_rotateright8(op, 1) == ror(uint8_t, op, 1));
  assert(__builtin_rotateright8(op, 2) == ror(uint8_t, op, 2));
  assert(__builtin_rotateright8(op, 3) == ror(uint8_t, op, 3));
  assert(__builtin_rotateright8(op, 4) == ror(uint8_t, op, 4));
}

void check_right16(void)
{
  uint16_t op;
  assert(__builtin_rotateright16(op, 1) == ror(uint16_t, op, 1));
  assert(__builtin_rotateright16(op, 2) == ror(uint16_t, op, 2));
  assert(__builtin_rotateright16(op, 3) == ror(uint16_t, op, 3));
  assert(__builtin_rotateright16(op, 4) == ror(uint16_t, op, 4));
}

void check_right32(void)
{
  uint32_t op;
  assert(__builtin_rotateright32(op, 1) == ror(uint32_t, op, 1));
  assert(__builtin_rotateright32(op, 2) == ror(uint32_t, op, 2));
  assert(__builtin_rotateright32(op, 3) == ror(uint32_t, op, 3));
  assert(__builtin_rotateright32(op, 4) == ror(uint32_t, op, 4));
}

void check_right64(void)
{
  uint64_t op;
  assert(__builtin_rotateright64(op, 1) == ror(uint64_t, op, 1));
  assert(__builtin_rotateright64(op, 2) == ror(uint64_t, op, 2));
  assert(__builtin_rotateright64(op, 3) == ror(uint64_t, op, 3));
  assert(__builtin_rotateright64(op, 4) == ror(uint64_t, op, 4));
}

int main(void)
{
  check_left8();
  check_left16();
  check_left32();
  check_left64();
  check_right8();
  check_right16();
  check_right32();
  check_right64();
}

#include <assert.h>

// GCC computes arithmetic on void * with a size of 1, and the result is a
// void * (GCC manual, "Arithmetic on void- and Function-Pointers").  Linux
// 5.10's ethtool_get_any_eeprom subtracts `useraddr + sizeof(eeprom)' from a
// void *, which goto-cc rejected ("pointer subtraction over different
// types"): void * + integer was typed char *.
int main()
{
  char buf[16];
  void *a = buf + 12, *b = buf;
  assert(a - (b + 8) == 4);
  assert((b + 8) - a == -4);
  assert(a - (8 + b) == 4);
  void *c = b;
  c += 4;
  assert(c == buf + 4);
  c -= 2;
  assert(c == buf + 2);
  assert(sizeof(b + 1) == sizeof(void *));
  assert(a - (b + 8) == 5);
  return 0;
}

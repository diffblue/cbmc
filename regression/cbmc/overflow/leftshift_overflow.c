#include <inttypes.h>

void leftshift_overflow1(unsigned char x)
{
  // signed, owing to promotion, and may overflow
  unsigned r = x << ((sizeof(unsigned) - 1) * 8 + 1);
}

void leftshift_overflow2(unsigned char x)
{
  // signed, owing to promotion, and cannot overflow
  unsigned r = x << ((sizeof(unsigned) - 1) * 8 - 1);
}

void leftshift_overflow3(unsigned char x)
{
  // unsigned
  unsigned r = (unsigned)x << ((sizeof(unsigned) - 1) * 8);
}

void leftshift_overflow4(unsigned char x)
{
  // negative value or zero, not an overflow
  int s = -x << ((sizeof(int) - 1) * 8);
}

void leftshift_overflow5(unsigned char x)
{
  // overflow
  int s = 1 << x;
}

int nondet_int();

void leftshift_overflow6(unsigned char x)
{
  // distance too far, not an overflow
  int s = nondet_int();
  int t = s << 100;
}

void leftshift_overflow7(unsigned char x)
{
  // not an overflow in ANSI-C, but undefined in C99
  int s = 1 << (sizeof(int) * 8 - 1);
}

void leftshift_overflow8(unsigned char x)
{
  // overflow in an expression where operand and distance types are different
  uint32_t u32;
  int64_t i64 = ((int64_t)u32) << 32;
}

unsigned char nondet_uchar();

int main()
{
  unsigned char x = nondet_uchar();

  switch(nondet_uchar())
  {
  case 1:
    leftshift_overflow1(x);
    break;
  case 2:
    leftshift_overflow2(x);
    break;
  case 3:
    leftshift_overflow3(x);
    break;
  case 4:
    leftshift_overflow4(x);
    break;
  case 5:
    leftshift_overflow5(x);
    break;
  case 6:
    leftshift_overflow6(x);
    break;
  case 7:
    leftshift_overflow7(x);
    break;
  case 8:
    leftshift_overflow8(x);
    break;
  }

  return 0;
}

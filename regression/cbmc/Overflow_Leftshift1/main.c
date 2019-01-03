int main()
{
  unsigned char x;

  // signed, owing to promotion, and may overflow
  unsigned r=x << ((sizeof(unsigned)-1)*8);

  // signed, owing to promotion, and cannot overflow
  r=x << ((sizeof(unsigned)-1)*8-1);

  // unsigned
  r=(unsigned)x << ((sizeof(unsigned)-1)*8);

  // negative value or zero, not an overflow
  int s = -x << ((sizeof(int) - 1) * 8);

  // overflow
  s = 1 << x;

  return 0;
}

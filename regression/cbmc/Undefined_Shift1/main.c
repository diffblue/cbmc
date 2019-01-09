void shift_distance_too_large()
{
  unsigned char x;
  unsigned r = x << ((sizeof(unsigned) - 1) * 8);  // ok
  r = x << ((sizeof(unsigned) - 1) * 8 - 1);       // ok
  r = (unsigned)x << ((sizeof(unsigned) - 1) * 8); // ok
  r = (unsigned)x << (sizeof(unsigned) * 8);       // too far
}

void shift_distance_negative()
{
  int dist;
  if(dist >= 10)
    dist = 10;
  unsigned r = 1 << dist; // distance may be negative
}

void negative_operand()
{
  int s = -1 << ((sizeof(int) - 1) * 8); // negative operand
}

int main()
{
  shift_distance_too_large();
  shift_distance_negative();
  negative_operand();
}

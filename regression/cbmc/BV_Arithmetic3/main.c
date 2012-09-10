unsigned char test_bit_reverse8(unsigned char v)
{
  unsigned char result = 0;
  int w = sizeof(char)*8;
  int i;
  for (i = 0; i < w; i++) {
    if (v & (1<<i))
      result |= 1<<(w-i-1);
  }
  return result;
}

int main()
{
  assert(test_bit_reverse8(127)==254);
}

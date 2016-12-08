int main()
{
  long dif;
  enum { BITS_TO_SHIFT = 8 * (sizeof(dif) - sizeof(int)) };
  /* shift leaving only "int" worth of bits */
  if (dif != 0) {
    dif = 1 | (int)(dif >> BITS_TO_SHIFT);
  }

  return 0;
}

class shift1
{
  public static void foo(int c, long x)
  {
    switch (c)
    {
    case 0:
      if (x == 5L) assert ((int)x << 1) == 10;
      break;
    case 1:
      if (x == 5L) assert ((int)x >> 1) == 2;
      break;
    case 2:
      if (x == -4L) assert ((int)x >> 1) == -2;
      break;
    case 3:
      if (x == -4L) assert ((int)x >>> 1) == 2147483646;
      break;
    case 4:
      if (x == 1L) assert ((int)x << 0) == 1;
      break;
    case 5:
      if (x == 1L) assert ((int)x << 31) == -2147483648;
      break;
    case 6:
      if (x == 1L) assert ((int)x << 32) == 1;
      break;
    case 7:
      if (x == 1L) assert ((int)x << 33) == 2;
      break;
    case 8:
      if (x == 1L) assert (x << 0) == 1L;
      break;
    case 9:
      if (x == 1L) assert (x << 63) == -9223372036854775808L;
      break;
    case 10:
      if (x == 1L) assert (x << 64) == 1L;
      break;
    default:
      if (x == 1L) assert (x << 65) == 2L;
      break;
    }
  }
}

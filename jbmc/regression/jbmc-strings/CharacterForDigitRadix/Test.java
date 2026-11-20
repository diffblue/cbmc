public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // the digit must be in the range 0 to radix - 1, and the radix in the range
    // 2 to 36
    case 0:
      assert Character.forDigit(10, 10) == '\0';
      break;
    case 1:
      assert Character.forDigit(-1, 10) == '\0';
      break;
    case 2:
      assert Character.forDigit(16, 16) == '\0';
      break;
    case 3:
      assert Character.forDigit(1, 37) == '\0';
      break;
    }
  }
}

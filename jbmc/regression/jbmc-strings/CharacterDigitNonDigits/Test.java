public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // characters that are not digits in any radix
    case 0:
      assert Character.digit('\0', 10) == -1;
      break;
    case 1:
      assert Character.digit(' ', 36) == -1;
      break;
    case 2:
      assert Character.digit('\u00b2', 10) == -1;
      break;
    case 3:
      assert Character.digit('\uff5b', 36) == -1;
      break;
    case 4:
      assert Character.getNumericValue(' ') == -1;
      break;
    // full-width letters
    case 5:
      assert Character.digit('\uff21', 16) == 10;
      break;
    case 6:
      assert Character.digit('\uff41', 36) == 10;
      break;
    case 7:
      assert Character.digit('\uff5a', 36) == 35;
      break;
    case 8:
      assert Character.digit('\uff5a', 16) == -1;
      break;
    }
  }
}

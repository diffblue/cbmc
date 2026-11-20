public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // numeric values of characters other than ASCII digits and letters
    case 0:
      assert Character.getNumericValue('\u00b2') == 2;
      break;
    case 1:
      assert Character.getNumericValue('\u00bc') == -2;
      break;
    case 2:
      assert Character.getNumericValue('\u2167') == 8;
      break;
    case 3:
      assert Character.getNumericValue('\uff11') == 1;
      break;
    case 4:
      assert Character.getNumericValue(0x1d7cf) == 1;
      break;
    }
  }
}

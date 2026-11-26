public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // letters other than ASCII ones
    case 0:
      assert Character.isLetter('\u00c0');
      break;
    case 1:
      assert Character.isLetter('\u4e00');
      break;
    case 2:
      assert Character.isLetter((int)'\u00c0');
      break;
    case 3:
      assert Character.isAlphabetic(0xc0);
      break;
    case 4:
      assert Character.isLetterOrDigit('\u00c0');
      break;
    case 5:
      assert Character.isLetterOrDigit((int)'\u4e00');
      break;
    }
  }
}

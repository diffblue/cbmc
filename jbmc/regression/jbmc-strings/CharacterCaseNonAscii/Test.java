public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // letters other than ASCII ones
    case 0:
      assert Character.isLowerCase('\u00df');
      break;
    case 1:
      assert Character.isLowerCase((int)'\u00e0');
      break;
    case 2:
      assert Character.isUpperCase('\u00c0');
      break;
    case 3:
      assert Character.isUpperCase((int)'\u0100');
      break;
    case 4:
      assert Character.toLowerCase('\u00c0') == '\u00e0';
      break;
    case 5:
      assert Character.toLowerCase((int)'\u0100') == '\u0101';
      break;
    case 6:
      assert Character.toUpperCase('\u00e0') == '\u00c0';
      break;
    case 7:
      assert Character.toUpperCase((int)'\u00ff') == '\u0178';
      break;
    case 8:
      assert Character.toTitleCase('\u00e0') == '\u00c0';
      break;
    }
  }
}

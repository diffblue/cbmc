public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // mirrored characters other than ASCII ones
    case 0:
      assert Character.isMirrored('\u00ab');
      break;
    case 1:
      assert Character.isMirrored('\u2208');
      break;
    case 2:
      assert Character.isMirrored((int)'\u2208');
      break;
    }
  }
}

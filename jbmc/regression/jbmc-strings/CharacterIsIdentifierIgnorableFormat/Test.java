public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // characters in the FORMAT general category
    case 0:
      assert Character.isIdentifierIgnorable('\u00ad');
      break;
    case 1:
      assert Character.isIdentifierIgnorable('\u200b');
      break;
    case 2:
      assert Character.isIdentifierIgnorable('\ufeff');
      break;
    case 3:
      assert Character.isIdentifierIgnorable((int)'\ufeff');
      break;
    }
  }
}

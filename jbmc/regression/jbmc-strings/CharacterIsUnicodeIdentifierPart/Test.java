public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // connecting punctuation and combining marks may be part of a Unicode
    // identifier
    case 0:
      assert Character.isUnicodeIdentifierPart('_');
      break;
    case 1:
      assert Character.isUnicodeIdentifierPart('\u0301');
      break;
    case 2:
      assert Character.isUnicodeIdentifierPart((int)'_');
      break;
    }
  }
}

public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // currency symbols and connecting punctuation may start a Java identifier
    case 0:
      assert Character.isJavaIdentifierStart('$');
      break;
    case 1:
      assert Character.isJavaIdentifierStart('\u00a2');
      break;
    case 2:
      assert Character.isJavaIdentifierStart('_');
      break;
    case 3:
      assert Character.isJavaIdentifierStart((int)'$');
      break;
    case 4:
      assert Character.isJavaLetter('$');
      break;
    // combining marks may be part of a Java identifier
    case 5:
      assert Character.isJavaIdentifierPart('$');
      break;
    case 6:
      assert Character.isJavaIdentifierPart('\u0301');
      break;
    case 7:
      assert Character.isJavaIdentifierPart((int)'\u0301');
      break;
    case 8:
      assert Character.isJavaLetterOrDigit('$');
      break;
    }
  }
}

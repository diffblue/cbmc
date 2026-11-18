public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    case 0:
      assert Character.getType('a') == Character.LOWERCASE_LETTER;
      break;
    case 1:
      assert Character.getType('A') == Character.UPPERCASE_LETTER;
      break;
    case 2:
      assert Character.getType((int)' ') == Character.SPACE_SEPARATOR;
      break;
    }
  }
}

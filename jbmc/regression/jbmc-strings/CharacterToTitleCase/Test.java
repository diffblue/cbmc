public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // characters without a titlecase mapping of their own map to uppercase
    case 0:
      assert Character.toTitleCase('a') == 'A';
      break;
    case 1:
      assert Character.toTitleCase('z') == 'Z';
      break;
    case 2:
      assert Character.toTitleCase('A') == 'A';
      break;
    case 3:
      assert Character.toTitleCase('1') == '1';
      break;
    case 4:
      assert Character.toTitleCase((int)'a') == 'A';
      break;
    // characters with a titlecase mapping of their own
    case 5:
      assert Character.toTitleCase('\u01c4') == '\u01c5';
      break;
    case 6:
      assert Character.toTitleCase('\u01c5') == '\u01c5';
      break;
    case 7:
      assert Character.toTitleCase('\u01c6') == '\u01c5';
      break;
    case 8:
      assert Character.toTitleCase('\u1f80') == '\u1f88';
      break;
    }
  }
}

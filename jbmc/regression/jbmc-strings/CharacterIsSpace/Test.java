public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    case 0:
      assert Character.isSpace(' ');
      break;
    case 1:
      assert Character.isSpace('\t');
      break;
    case 2:
      assert Character.isSpace('\n');
      break;
    case 3:
      assert Character.isSpace('\f');
      break;
    case 4:
      assert Character.isSpace('\r');
      break;
    // white space according to isWhitespace, but not according to isSpace
    case 5:
      assert !Character.isSpace('\u000b');
      break;
    case 6:
      assert !Character.isSpace('\u001c');
      break;
    case 7:
      assert !Character.isSpace('\u2028');
      break;
    case 8:
      assert !Character.isSpace('\u3000');
      break;
    }
  }
}

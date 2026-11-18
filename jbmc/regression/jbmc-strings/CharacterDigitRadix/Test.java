public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // the radix must be in the range 2 to 36
    case 0:
      assert Character.digit('0', 1) == -1;
      break;
    case 1:
      assert Character.digit('1', 37) == -1;
      break;
    case 2:
      assert Character.digit((int)'1', 37) == -1;
      break;
    }
  }
}

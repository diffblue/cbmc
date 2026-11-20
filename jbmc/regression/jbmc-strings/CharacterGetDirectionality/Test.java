public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    case 0:
      assert Character.getDirectionality('a') == Character.DIRECTIONALITY_LEFT_TO_RIGHT;
      break;
    case 1:
      assert Character.getDirectionality('0') == Character.DIRECTIONALITY_EUROPEAN_NUMBER;
      break;
    case 2:
      assert Character.getDirectionality((int)'a') == Character.DIRECTIONALITY_LEFT_TO_RIGHT;
      break;
    }
  }
}

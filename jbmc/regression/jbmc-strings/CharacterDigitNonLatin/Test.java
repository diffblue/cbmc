public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // digits other than the latin ones
    case 0:
      assert Character.digit('\u0661', 10) == 1;
      break;
    case 1:
      assert Character.digit('\uff11', 10) == 1;
      break;
    case 2:
      assert Character.digit(0x1d7cf, 10) == 1;
      break;
    }
  }
}

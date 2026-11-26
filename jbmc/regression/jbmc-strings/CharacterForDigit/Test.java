public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    case 0:
      assert Character.forDigit(9, 16) == '9';
      break;
    case 1:
      assert Character.forDigit(10, 16) == 'a';
      break;
    case 2:
      assert Character.forDigit(11, 16) == 'b';
      break;
    case 3:
      assert Character.forDigit(35, 36) == 'z';
      break;
    }
  }
}

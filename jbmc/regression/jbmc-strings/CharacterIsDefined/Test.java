public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // not characters
    case 0:
      assert !Character.isDefined(-1);
      break;
    case 1:
      assert !Character.isDefined(0xffff);
      break;
    // characters defined in more recent versions of Unicode
    case 2:
      assert Character.isDefined('\u0750');
      break;
    case 3:
      assert Character.isDefined(0x10140);
      break;
    case 4:
      assert Character.isDefined(0x1f600);
      break;
    }
  }
}

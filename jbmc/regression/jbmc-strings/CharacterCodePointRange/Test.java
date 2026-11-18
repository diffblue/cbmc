public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // valid code points are 0 to 0x10FFFF
    case 0:
      assert !Character.isValidCodePoint(-1);
      break;
    case 1:
      assert Character.isValidCodePoint(0);
      break;
    case 2:
      assert Character.isValidCodePoint(0x10FFFF);
      break;
    case 3:
      assert !Character.isValidCodePoint(0x110000);
      break;
    // supplementary code points are 0x10000 to 0x10FFFF
    case 4:
      assert !Character.isSupplementaryCodePoint(0xFFFF);
      break;
    case 5:
      assert Character.isSupplementaryCodePoint(0x10000);
      break;
    case 6:
      assert Character.isSupplementaryCodePoint(0x10FFFF);
      break;
    case 7:
      assert !Character.isSupplementaryCodePoint(0x110000);
      break;
    case 8:
      assert !Character.isSupplementaryCodePoint(-1);
      break;
    }
  }
}

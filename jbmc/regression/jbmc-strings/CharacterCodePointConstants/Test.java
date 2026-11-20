public class Test
{
  // each case is checked on a path of its own (k is nondeterministic)
  static void check(int k)
  {
    switch(k)
    {
    // defined characters whose codes are the low 16 bits of bounds of ranges of
    // undefined code points beyond 0xFFFF
    case 0:
      assert Character.isDefined((char)0x01C5);
      break;
    case 1:
      assert Character.isDefined((char)0x4E00);
      break;
    // characters that are not identifier characters, while the code points that
    // are 0x10000 larger are letter numbers
    case 2:
      assert !Character.isUnicodeIdentifierStart((char)0x2400);
      break;
    case 3:
      assert !Character.isUnicodeIdentifierPart((char)0x2410);
      break;
    case 4:
      assert !Character.isJavaIdentifierStart((char)0x2460);
      break;
    case 5:
      assert !Character.isJavaIdentifierPart((char)0x246E);
      break;
    }
  }
}

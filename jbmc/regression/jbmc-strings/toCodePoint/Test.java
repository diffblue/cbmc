public class Test {

  public void test(char a, char b) {
    assert Character.toCodePoint((char)0xD800, (char)0xDC00) == 0x10000;
    assert Character.toCodePoint((char)0xDBFF, (char)0xDFFF) == 0x10ffff;
    assert Character.toCodePoint((char)0xD800, (char)0xDFFF) == 0x103ff;
    assert Character.toCodePoint((char)0xDBFF, (char)0xDC00) == 0x10fc00;
    assert Character.toCodePoint(a, b) == 0x10000;
  }
}

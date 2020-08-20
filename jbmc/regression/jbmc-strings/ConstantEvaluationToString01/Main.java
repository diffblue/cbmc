import org.cprover.CProverString;
import org.cprover.CProver;

public class Main {
  public void testIntToString() {
    assert CProverString.toString(0).equals("0");
    assert CProverString.toString(1).equals("1");
    assert CProverString.toString(-1).equals("-1");
    assert CProverString.toString(Integer.MIN_VALUE).equals("-2147483648");
    assert CProverString.toString(Integer.MAX_VALUE).equals("2147483647");
  }

  public void testIntToStringWithRadixTwo() {
    assert CProverString.toString(0, 2).equals("0");
    assert CProverString.toString(1, 2).equals("1");
    assert CProverString.toString(-1, 2).equals("-1");
    assert CProverString.toString(0b101011, 2).equals("101011");
    assert CProverString.toString(Integer.MIN_VALUE, 2)
        .equals("-10000000000000000000000000000000");
    assert CProverString.toString(Integer.MAX_VALUE, 2)
        .equals("1111111111111111111111111111111");
  }

  public void testIntToStringWithRadixSixteen() {
    assert CProverString.toString(0, 16).equals("0");
    assert CProverString.toString(1, 16).equals("1");
    assert CProverString.toString(-1, 16).equals("-1");
    assert CProverString.toString(0x3f08, 16).equals("3f08");
    assert CProverString.toString(Integer.MIN_VALUE, 16).equals("-80000000");
    assert CProverString.toString(Integer.MAX_VALUE, 16).equals("7fffffff");
  }

  public void testIntToStringNoPropagation1(int i) {
    assert CProverString.toString(i).equals("0");
  }

  public void testIntToStringNoPropagation2(int radix) {
    CProver.assume(radix == 2 || radix == 8 || radix == 10 || radix == 16);
    assert CProverString.toString(0, radix).equals("0");
  }

  public void testLongToString() {
    assert CProverString.toString(0L).equals("0");
    assert CProverString.toString(1L).equals("1");
    assert CProverString.toString(-1L).equals("-1");
    assert CProverString.toString(Long.MIN_VALUE)
        .equals("-9223372036854775808");
    assert CProverString.toString(Long.MAX_VALUE).equals("9223372036854775807");
  }

  public void testLongToStringWithRadixTwo() {
    assert CProverString.toString(0L, 2).equals("0");
    assert CProverString.toString(1L, 2).equals("1");
    assert CProverString.toString(-1L, 2).equals("-1");
    assert CProverString.toString(Long.MIN_VALUE, 2)
        .equals(
            "-1000000000000000000000000000000000000000000000000000000000000000");
    assert CProverString.toString(Long.MAX_VALUE, 2)
        .equals(
            "111111111111111111111111111111111111111111111111111111111111111");
  }

  public void testLongToStringWithRadixSixteen() {
    assert CProverString.toString(0L, 16).equals("0");
    assert CProverString.toString(1L, 16).equals("1");
    assert CProverString.toString(-1L, 16).equals("-1");
    assert CProverString.toString(Long.MIN_VALUE, 16)
        .equals("-8000000000000000");
    assert CProverString.toString(Long.MAX_VALUE, 16)
        .equals("7fffffffffffffff");
  }

  public void testLongToStringNoPropagation1(long l) {
    assert CProverString.toString(l).equals("0");
  }

  public void testLongToStringNoPropagation2(int radix) {
    CProver.assume(radix == 2 || radix == 8 || radix == 10 || radix == 16);
    assert CProverString.toString(0L, radix).equals("0");
  }

  public void testFloatToString() {
    assert CProverString.toString(0F).equals("0.0");
    assert CProverString.toString(1F).equals("1.0");
    assert CProverString.toString(1.1F).equals("1.1");
    assert CProverString.toString(Float.MAX_VALUE).equals("3.4028235E38");
    assert CProverString.toString(Float.MIN_VALUE).equals("1.4E-45");
    assert CProverString.toString(Float.POSITIVE_INFINITY).equals("Infinity");
    assert CProverString.toString(Float.NEGATIVE_INFINITY).equals("-Infinity");
    assert CProverString.toString(Float.NaN).equals("NaN");
  }

  public void testFloatToStringNoPropagation(float f) {
    assert CProverString.toString(f).equals("0.0");
  }
}

public class BoxingLambda {

  interface TakesBoxedBoolean {
    public Boolean accept(Boolean b);
  }

  interface TakesUnboxedBoolean {
    public boolean accept(boolean b);
  }

  interface TakesBoxedByte {
    public Byte accept(Byte b);
  }

  interface TakesUnboxedByte {
    public byte accept(byte b);
  }

  interface TakesBoxedCharacter {
    public Character accept(Character c);
  }

  interface TakesUnboxedCharacter {
    public char accept(char c);
  }

  interface TakesBoxedDouble {
    public Double accept(Double d);
  }

  interface TakesUnboxedDouble {
    public double accept(double d);
  }

  interface TakesBoxedFloat {
    public Float accept(Float f);
  }

  interface TakesUnboxedFloat {
    public float accept(float f);
  }

  interface TakesBoxedInteger {
    public Integer accept(Integer i);
  }

  interface TakesUnboxedInteger {
    public int accept(int i);
  }

  interface TakesBoxedLong {
    public Long accept(Long l);
  }

  interface TakesUnboxedLong {
    public long accept(long l);
  }

  interface TakesBoxedShort {
    public Short accept(Short s);
  }

  interface TakesUnboxedShort {
    public short accept(short s);
  }

  public static void testBoolean() {

    TakesBoxedBoolean takesBoxed = b -> !b;
    TakesUnboxedBoolean takesUnboxed = takesBoxed::accept;
    TakesBoxedBoolean takesBoxedAgain = takesUnboxed::accept;

    assert takesBoxed.accept(true) == false;
    assert takesUnboxed.accept(true) == false;
    assert takesBoxedAgain.accept(true) == false;
    assert false;

  }

  public static void testByte() {

    TakesBoxedByte takesBoxed = b -> (byte)(b + 1);
    TakesUnboxedByte takesUnboxed = takesBoxed::accept;
    TakesBoxedByte takesBoxedAgain = takesUnboxed::accept;

    assert takesBoxed.accept((byte)1) == 2;
    assert takesUnboxed.accept((byte)1) == 2;
    assert takesBoxedAgain.accept((byte)1) == 2;
    assert false;

  }

  public static void testCharacter() {

    TakesBoxedCharacter takesBoxed = c -> c == 'a' ? 'b' : 'a';
    TakesUnboxedCharacter takesUnboxed = takesBoxed::accept;
    TakesBoxedCharacter takesBoxedAgain = takesUnboxed::accept;

    assert takesBoxed.accept('a') == 'b';
    assert takesUnboxed.accept('a') == 'b';
    assert takesBoxedAgain.accept('a') == 'b';
    assert false;

  }

  public static void testDouble() {

    TakesBoxedDouble takesBoxed = d -> d + 1;
    TakesUnboxedDouble takesUnboxed = takesBoxed::accept;
    TakesBoxedDouble takesBoxedAgain = takesUnboxed::accept;

    assert takesBoxed.accept(1.0) == 2.0;
    assert takesUnboxed.accept(1.0) == 2.0;
    assert takesBoxedAgain.accept(1.0) == 2.0;
    assert false;

  }

  public static void testFloat() {

    TakesBoxedFloat takesBoxed = f -> f + 1;
    TakesUnboxedFloat takesUnboxed = takesBoxed::accept;
    TakesBoxedFloat takesBoxedAgain = takesUnboxed::accept;

    assert takesBoxed.accept(1.0f) == 2.0f;
    assert takesUnboxed.accept(1.0f) == 2.0f;
    assert takesBoxedAgain.accept(1.0f) == 2.0f;
    assert false;

  }

  public static void testInteger() {

    TakesBoxedInteger takesBoxed = i -> i + 1;
    TakesUnboxedInteger takesUnboxed = takesBoxed::accept;
    TakesBoxedInteger takesBoxedAgain = takesUnboxed::accept;

    assert takesBoxed.accept(1) == 2;
    assert takesUnboxed.accept(1) == 2;
    assert takesBoxedAgain.accept(1) == 2;
    assert false;

  }

  public static void testLong() {

    TakesBoxedLong takesBoxed = l -> l + 1;
    TakesUnboxedLong takesUnboxed = takesBoxed::accept;
    TakesBoxedLong takesBoxedAgain = takesUnboxed::accept;

    assert takesBoxed.accept(1L) == 2L;
    assert takesUnboxed.accept(1L) == 2L;
    assert takesBoxedAgain.accept(1L) == 2L;
    assert false;

  }

  public static void testShort() {

    TakesBoxedShort takesBoxed = s -> (short)(s + 1);
    TakesUnboxedShort takesUnboxed = takesBoxed::accept;
    TakesBoxedShort takesBoxedAgain = takesUnboxed::accept;

    assert takesBoxed.accept((short)1) == 2;
    assert takesUnboxed.accept((short)1) == 2;
    assert takesBoxedAgain.accept((short)1) == 2;
    assert false;

  }

}

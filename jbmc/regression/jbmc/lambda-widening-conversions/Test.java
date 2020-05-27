public class Test {

  // Tests for widening a parameter:

  public interface ByteToLong {
    public long accept(byte b);
  }

  public interface ShortToLong {
    public long accept(short s);
  }

  public interface IntToLong {
    public long accept(int i);
  }

  public interface FloatToDouble {
    public double accept(float f);
  }

  public static long longToLong(long x) { return x + 1L; }
  public static double doubleToDouble(double x) { return x + 1.0; }

  public static void testByteToLong() {
    ByteToLong b2l = Test::longToLong;
    assert b2l.accept((byte)1) == 2L;
    assert false;
  }

  public static void testShortToLong() {
    ShortToLong s2l = Test::longToLong;
    assert s2l.accept((short)1) == 2L;
    assert false;
  }

  public static void testIntToLong() {
    IntToLong i2l = Test::longToLong;
    assert i2l.accept(1) == 2L;
    assert false;
  }

  public static void testFloatToDouble() {
    FloatToDouble f2d = Test::doubleToDouble;
    assert f2d.accept(1.0f) == 2.0;
    assert false;
  }

  // Tests for widening a return value:

  public interface LongToLong {
    public long accept(long l);
  }

  public static byte longToByte(long l) { return (byte)(l + 1); }
  public static short longToShort(long l) { return (short)(l + 1); }
  public static int longToInt(long l) { return (int)(l + 1); }

  public interface DoubleToDouble {
    public double accept(double d);
  }

  public static float doubleToFloat(double d) { return (float)(d + 1); }

  public static void testDoubleToFloat() {
    DoubleToDouble d2d = Test::doubleToFloat;
    assert d2d.accept(1.0) == 2.0;
    assert false;
  }

  public static void testLongToByte() {
    LongToLong l2l = Test::longToByte;
    assert l2l.accept(1L) == 2L;
    assert false;
  }

  public static void testLongToShort() {
    LongToLong l2l = Test::longToShort;
    assert l2l.accept(1L) == 2L;
    assert false;
  }

  public static void testLongToInt() {
    LongToLong l2l = Test::longToInt;
    assert l2l.accept(1L) == 2L;
    assert false;
  }

}

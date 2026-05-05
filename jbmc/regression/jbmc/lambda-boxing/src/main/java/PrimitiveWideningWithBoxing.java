public class PrimitiveWideningWithBoxing {

  // Tests for widening a parameter, accompanied by boxing and unboxing:

  public interface ByteToLong {
    public Long accept(Byte b);
  }

  public interface ShortToLong {
    public Long accept(Short s);
  }

  public interface IntToLong {
    public Long accept(Integer i);
  }

  public interface FloatToDouble {
    public Double accept(Float f);
  }

  public static long longToLong(long x) { return x + 1L; }
  public static double doubleToDouble(double x) { return x + 1.0; }

  public static void testByteToLong() {
    ByteToLong b2l = PrimitiveWideningWithBoxing::longToLong;
    assert b2l.accept((byte)1) == 2L;
    assert false;
  }

  public static void testShortToLong() {
    ShortToLong s2l = PrimitiveWideningWithBoxing::longToLong;
    assert s2l.accept((short)1) == 2L;
    assert false;
  }

  public static void testIntToLong() {
    IntToLong i2l = PrimitiveWideningWithBoxing::longToLong;
    assert i2l.accept(1) == 2L;
    assert false;
  }

  public static void testFloatToDouble() {
    FloatToDouble f2d = PrimitiveWideningWithBoxing::doubleToDouble;
    assert f2d.accept(1.0f) == 2.0;
    assert false;
  }

  // Tests for widening a return value, accompanied by boxing and unboxing:

  public interface LongToLong {
    public long accept(long l);
  }

  public static Byte longToByte(Long l) { return (byte)(l + 1); }
  public static Short longToShort(Long l) { return (short)(l + 1); }
  public static Integer longToInt(Long l) { return (int)(l + 1); }

  public interface DoubleToDouble {
    public double accept(double d);
  }

  public static Float doubleToFloat(Double d) { return (float)(d + 1); }

  public static void testDoubleToFloat() {
    DoubleToDouble d2d = PrimitiveWideningWithBoxing::doubleToFloat;
    assert d2d.accept(1.0) == 2.0;
    assert false;
  }

  public static void testLongToByte() {
    LongToLong l2l = PrimitiveWideningWithBoxing::longToByte;
    assert l2l.accept(1L) == 2L;
    assert false;
  }

  public static void testLongToShort() {
    LongToLong l2l = PrimitiveWideningWithBoxing::longToShort;
    assert l2l.accept(1L) == 2L;
    assert false;
  }

  public static void testLongToInt() {
    LongToLong l2l = PrimitiveWideningWithBoxing::longToInt;
    assert l2l.accept(1L) == 2L;
    assert false;
  }

}

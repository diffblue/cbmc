public class ArrayClone {
  public static void cloneReferenceArray() {
    ArrayClone[] a = {new ArrayClone(), new ArrayClone() };
    ArrayClone[] clone = a.clone();

    assert(a.length == clone.length);
    assert(a[0] == clone[0]);
    assert(a[1] == clone[1]);
    assert(a != clone);
  }

  public static void cloneObjectArray() {
    Object[] a = {new Object(), new Object() };
    Object[] clone = a.clone();

    assert(a.length == clone.length);
    assert(a[0] == clone[0]);
    assert(a[1] == clone[1]);
    assert(a != clone);
  }

  public static void cloneByteArray() {
    byte[] a = {(byte) 1, (byte) 2};
    byte[] clone = a.clone();

    assert(a.length == clone.length);
    assert(a[0] == clone[0]);
    assert(a[1] == clone[1]);
    assert(a != clone);
  }

  public static void cloneShortArray() {
    short[] a = {(short) 1, (short) 2};
    short[] clone = a.clone();

    assert(a.length == clone.length);
    assert(a[0] == clone[0]);
    assert(a[1] == clone[1]);
    assert(a != clone);
  }

  public static void cloneIntArray() {
    int[] a = {1, 2};
    int[] clone = a.clone();

    assert(a.length == clone.length);
    assert(a[0] == clone[0]);
    assert(a[1] == clone[1]);
    assert(a != clone);
  }

  public static void cloneLongArray() {
    long[] a = {1L, 2L };
    long[] clone = a.clone();

    assert(a.length == clone.length);
    assert(a[0] == clone[0]);
    assert(a[1] == clone[1]);
    assert(a != clone);
  }

    public static void cloneFloatArray() {
    float[] a = {1.0f, 2.0f};
    float[] clone = a.clone();

    assert(a.length == clone.length);
    assert(a[0] == clone[0]);
    assert(a[1] == clone[1]);
    assert(a != clone);
  }

  public static void cloneDoubleArray() {
    double[] a = {1.0, 2.0};
    double[] clone = a.clone();

    assert(a.length == clone.length);
    assert(a[0] == clone[0]);
    assert(a[1] == clone[1]);
    assert(a != clone);
  }

  public static void cloneBooleanArray() {
    boolean[] a = {true, false};
    boolean[] clone = a.clone();

    assert(a.length == clone.length);
    assert(a[0] == clone[0]);
    assert(a[1] == clone[1]);
    assert(a != clone);
  }

}

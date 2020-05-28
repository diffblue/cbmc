public class Test {

  interface TakesT<T> {
    public Object take(T t);
  }

  interface YieldsT<T> {
    public T yield();
  }

  interface TakesInt {
    public Object take(int i);
  }

  interface TakesLong {
    public Object take(long l);
  }

  interface YieldsInt {
    public int yield();
  }

  public static Object takesLong(long l) { return l; }

  public static short yieldsShort() { return (short)1; }

  public static void test() {

    // Implement a generic interface using a primitive-typed function
    // that requires us to unbox the Short then widen it:
    TakesT<Short> takesShort = Test::takesLong;
    assert takesShort.take((short)1).equals(1L);

    // Surprisingly, the following case doesn't compile despite
    // being type-safe and symmetrical to the one above:
    // YieldsT<Long> yieldsLong = Test::yieldsShort;

    // So instead, here's a simpler case, that just requires us
    // to box the return value, not widen it then box:
    YieldsT<Short> yieldsShort = Test::yieldsShort;
    assert yieldsShort.yield() == (short)1;

    // Now test the reverse: using an instantiated generic to
    // implement a primitive-typed interface:

    TakesT<Long> takesLong = x -> x + 1;
    // Again this doesn't compile:
    // TakesInt takesInt = takesLong::take;
    // So here's a simpler example that only boxes to implement the
    // primitive interface, rather than boxes then widens:
    TakesLong takesPrimitiveLong = takesLong::take;
    assert takesPrimitiveLong.take(1L).equals(2L);

    // And finally, using an instantiated generic to satisfy a primitive
    // return value. This one does work with the conversion requiring both
    // to unbox the value and to widen it.
    YieldsT<Short> yieldsShortGeneric = () -> (short)1;
    YieldsInt yieldsInt = yieldsShortGeneric::yield;
    assert yieldsInt.yield() == 1;

    // Check we got to the end:
    assert false;

  }

}

public class BoxingWithOtherConversions {

  interface ObjectToObject {
    Object accept(Object o);
  }

  interface IntToObject {
    Object accept(int i);
  }

  // Check we can narrow a parameter type down to a primitive
  // which should be boxed and then upcast to Object by the
  // generated lambda:
  public static void testNarrowParameterTypeToPrimitive() {
    ObjectToObject o2o = i -> ((Integer)i) + 1;
    IntToObject i2o = o2o::accept;
    assert o2o.accept(1).equals(2);
    assert i2o.accept(1).equals(2);
    assert false;
  }

  interface ObjectToInt {
    int accept(Object o);
  }

  public static void testBroadenReturnTypeToObject() {
    ObjectToInt o2i = o -> ((Integer)o).intValue() + 1;
    ObjectToObject o2o = o2i::accept;
    assert o2o.accept(1).equals(2);
    assert o2i.accept(1) == 2;
    assert false;
  }
}

public class GenericFunctions
{
  public static <T> void processSimpleGeneric(SimpleGeneric<T> x) {
    assert(x.t==null);
  }

  // Test a wildcard generic bound by an interface
  public static <T extends BasicInterface> void processUpperBoundInterfaceGeneric(SimpleGeneric<T> x) {
    assert(x.t.getX() == 4);
  }

  // Test a wild card generic bound by a class
  public static <T extends Foo> void processUpperBoundClassGeneric(SimpleGeneric<T> x) {
    assert(x.t.getX() == 4);
  }

  // Test a wild card generic bound by a class and an interface
  public static <T extends Foo & BasicInterface> void processDoubleUpperBoundClassGeneric(SimpleGeneric<T> x) {
    assert(x.t.getX() == 4);
  }

  // Test a wild card generic bound by two interfaces
  public static <T extends BasicInterface & BasicInterfaceCopy> void processDoubleUpperBoundInterfaceGeneric(SimpleGeneric<T> x) {
      assert(x.t.getX() == 4);
  }
}

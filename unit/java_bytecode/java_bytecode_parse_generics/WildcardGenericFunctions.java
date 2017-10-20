public class WildcardGenericFunctions
{
  // Test a wild card generic type
  public static void processSimpleGeneric(Generic<?> x) {
    assert(x.t.equals(null));
  }

  // Test a wildcard generic bound by an interface
  public static void processUpperBoundInterfaceGeneric(Generic<? extends
  Interface> x) {
    assert(x.t.getX() == 4);
  }

  // Test a wild card generic bound by a class
  public static void processUpperBoundClassGeneric(Generic<? extends
  Interface_Implementation> x) {
    assert(x.t.getX() == 4);
  }

  // It isn't legal to have a wild card with two upper bounds
  // Per language spec on intersection types

  public static void processLowerBoundGeneric(Generic<? super
  Interface_Implementation> x, Interface_Implementation assign) {
    x.t = assign;
  }

  // It is not legal Java to specify both an upper and lower bound
  // public static void processBoundSuperClassGeneric(Generic<? extends Object super Interface_Implementation> x, Interface_Implementation assign) {
  //   x.t = assign;
  // }

  // Test a wild card generic bound by a class
  // public static void processBoundClassGenericDoubleBound(Generic<? extends Interface_Implementation & Interface> x) {
  //   assert(x.t.getX() == 4);
  // }

  public static void test()
  {
    Generic<Interface_Implementation> myGenericValue = new Generic<Interface_Implementation>();
    myGenericValue.t = null;
    processSimpleGeneric(myGenericValue);

    myGenericValue.t = new Interface_Implementation();
    myGenericValue.t.x = 4;
    processUpperBoundInterfaceGeneric(myGenericValue);

    Generic<Interface_Implementation_Derived> anotherGenericValue = new Generic<Interface_Implementation_Derived>();
    anotherGenericValue.t = new Interface_Implementation_Derived();
    anotherGenericValue.t.x = 4;
    processUpperBoundClassGeneric(anotherGenericValue);


    Generic<Object> baseGenericValue = new Generic<Object>();
    processLowerBoundGeneric(baseGenericValue, new Interface_Implementation());
  }
}

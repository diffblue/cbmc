interface BasicInterface
{
  int getX();
}

class Foo implements BasicInterface
{
  public int x;

  public int getX() {
    return x;
  }
}

class Bar extends Foo
{}

class SimpleGeneric<T>
{
  public T t;
}

public class WildcardGenericFunctions
{
  // Test a wild card generic type
  public static void processSimpleGeneric(SimpleGeneric<?> x) {
    assert(x.t.equals(null));
  }

  // Test a wildcard generic bound by an interface
  public static void processUpperBoundInterfaceGeneric(SimpleGeneric<? extends BasicInterface> x) {
    assert(x.t.getX() == 4);
  }

  // Test a wild card generic bound by a class
  public static void processUpperBoundClassGeneric(SimpleGeneric<? extends Foo> x) {
    assert(x.t.getX() == 4);
  }

  // It isn't legal to have an wild card with two upper bounds
  // Per language spec on intersection types

  public static void processLowerBoundGeneric(SimpleGeneric<? super Foo> x, Foo assign) {
    x.t = assign;
  }

  // It is not legal Java to specify both an upper and lower bound
  // public static void processBoundSuperClassGeneric(SimpleGeneric<? extends Object super Foo> x, Foo assign) {
  //   x.t = assign;
  // }

  // Test a wild card generic bound by a class
  // public static void processBoundClassGenericDoubleBound(SimpleGeneric<? extends Foo & BasicInterface> x) {
  //   assert(x.t.getX() == 4);
  // }

  public static void test()
  {
    SimpleGeneric<Foo> myGenericValue = new SimpleGeneric<Foo>();
    myGenericValue.t = null;
    processSimpleGeneric(myGenericValue);

    myGenericValue.t = new Foo();
    myGenericValue.t.x = 4;
    processUpperBoundInterfaceGeneric(myGenericValue);

    SimpleGeneric<Bar> anotherGenericValue = new SimpleGeneric<Bar>();
    anotherGenericValue.t = new Bar();
    anotherGenericValue.t.x = 4;
    processUpperBoundClassGeneric(anotherGenericValue);


    SimpleGeneric<Object> baseGenericValue = new SimpleGeneric<Object>();
    processLowerBoundGeneric(baseGenericValue, new Foo());
  }
}
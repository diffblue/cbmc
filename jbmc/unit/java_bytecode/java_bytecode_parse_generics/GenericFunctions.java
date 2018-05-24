public class GenericFunctions
{

  //Methods with generic inputs
  public static <T> void processSimple(Generic<T> x)
  {

  }

  public static <T extends Interface> void processUpperBoundInterface(Generic<T> x)
  {

  }

  public static <T extends Interface_Implementation> void processUpperBoundClass(Generic<T> x)
  {

  }

  public static <T extends java.lang.Number> void processUpperBoundClass2(T x)
  {

  }

  public static <T extends Interface_Implementation & Interface> void processDoubleUpperBoundClass(Generic<T> x)
  {

  }

  public static <T extends Interface & Interface_Copy> void processDoubleUpperBoundInterface(Generic<T> x)
  {
      
  }

  public static <T,U> void processMultipleSimple(Generic<T> t, Generic<U> u)
  {

  }

  public static <T extends Interface,U extends Interface_Implementation & Interface> void processMultipleUpperBound(Generic<T> t, Generic<U> u)
  {

  }

  //Methods with generic output
  public static <T> Generic<T> returnSimple()
  {
    Generic<T> x=new Generic<T>();
    return x;
  }

  public static <T> T returnSimpleField()
  {
    Generic<T> x=new Generic<T>();
    return x.t;
  }

  public static <T extends Interface> Generic<T> returnUpperBoundInterface()
  {
    Generic<T> x=new Generic<T>();
    return x;
  }

  public static <T extends Interface_Implementation> Generic<T> returnUpperBoundClass()
  {
    Generic<T> x=new Generic<T>();
    return x;
  }

  public static <T extends Interface_Implementation & Interface> Generic<T> returnDoubleUpperBoundClass()
  {
    Generic<T> x=new Generic<T>();
    return x;
  }

  public static <T extends Interface & Interface_Copy> Generic<T> returnDoubleUpperBoundInterface()
  {
    Generic<T> x=new Generic<T>();
    return x;
  }

  //Methods with generic input and output
  public static <T> Generic<T> processReturnSimpleSame(Generic<T> x)
  {
    return x;
  }

  public static <T extends Interface> Generic<T> processReturnUpperBoundInterfaceSame(Generic<T> x)
  {
    return x;
  }

  public static <T extends Interface_Implementation> Generic<T> processReturnUpperBoundClassSame(Generic<T> x)
  {
    return x;
  }

  public static <T extends Interface_Implementation & Interface> Generic<T> processReturnDoubleUpperBoundClassSame(Generic<T> x)
  {
    return x;
  }

  public static <T extends Interface & Interface_Copy> Generic<T> processReturnDoubleUpperBoundInterfaceSame(Generic<T> x)
  {
    return x;
  }

  public static <T,U> Generic<T> processReturnSimpleDifferent(Generic<U> u)
  {
    Generic<T> t=new Generic<T>();
    return t;
  }

  public static <T extends Interface,U extends Interface_Implementation & Interface> Generic<T> processReturnUpperBoundDifferent(Generic<U> u)
  {
    Generic<T> t=new Generic<T>();
    return t;
  }

  public static <T,U,V> Generic<T> processReturnMultipleSimpleDifferent(Generic<U> u, Generic<V> v)
  {
    Generic<T> t=new Generic<T>();
    return t;
  }

  public static <T extends Interface,U extends Interface_Implementation & Interface, V extends Interface_Copy> Generic<T> processReturnMultipleUpperBoundDifferent(Generic<U> u, Generic<V> v)
  {
    Generic<T> t=new Generic<T>();
    return t;
  }
}

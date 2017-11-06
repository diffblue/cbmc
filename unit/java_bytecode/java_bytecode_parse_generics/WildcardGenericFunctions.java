public class WildcardGenericFunctions
{
  // Test a wild card generic type
  public static void processSimpleGeneric(Generic<?> x)
  {

  }

  // Test a wildcard generic bound by an interface
  public static void processUpperBoundInterfaceGeneric(
    Generic<? extends Interface> x)
  {

  }

  // Test a wild card generic bound by a class
  public static void processUpperBoundClassGeneric(
    Generic<? extends Interface_Implementation> x)
  {

  }

  // It isn't legal to have a wild card with two upper bounds
  // Per language spec on intersection types

  public static void processLowerBoundGeneric(
    Generic<? super Interface_Implementation> x,
    Interface_Implementation assign)
  {

  }

  // It is not legal Java to specify both an upper and lower bound
  // public static void processBoundSuperClassGeneric(
  //   Generic<? extends Object super Interface_Implementation> x,
  //   Interface_Implementation assign)
  // {
  //
  // }

  // It is not legal Java to specify two upper bounds
  // Test a wild card generic bound by a class and an interface
  // public static void processBoundClassGenericDoubleBound(
  //   Generic<? extends Interface_Implementation & Interface> x)
  // {
  //
  // }
}

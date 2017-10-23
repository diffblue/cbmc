public class GenericFunctions
{
  public static <T> void processSimpleGeneric(Generic<T> x)
  {

  }

  // Test a wildcard generic bound by an interface
  public static <T extends Interface> void processUpperBoundInterfaceGeneric(Generic<T> x)
  {

  }

  // Test a wild card generic bound by a class
  public static <T extends Interface_Implementation> void processUpperBoundClassGeneric(Generic<T> x)
  {

  }

  // Test a wild card generic bound by a class and an interface
  public static <T extends Interface_Implementation & Interface> void processDoubleUpperBoundClassGeneric(Generic<T> x)
  {

  }

  // Test a wild card generic bound by two interfaces
  public static <T extends Interface & Interface_Copy> void processDoubleUpperBoundInterfaceGeneric(Generic<T> x)
  {
      
  }
}

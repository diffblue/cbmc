public class FunctionsWithGenerics
{

  class Inner
  {
    public Generic<Integer> x;
  }

  public static Generic<Integer> processReturnSame(Generic<Integer> x)
  {
    return x;
  }

  public static Generic<Integer> processReturnDifferent(Generic<String> s)
  {
    Generic<Integer> x = new Generic<Integer>();
    return x;
  }

  public static Generic<Integer> processReturnMultipleSame(Generic<Integer> x, Generic<Integer> y)
  {
    return x;
  }

  public static Generic<Integer> processReturnMultipleDifferent(Generic<String> s, Generic<Boolean> b)
  {
    Generic<Integer> x = new Generic<Integer>();
    return x;
  }

  public Generic<Integer> returnInnerField(Inner inner)
  {
    return inner.x;
  }

}

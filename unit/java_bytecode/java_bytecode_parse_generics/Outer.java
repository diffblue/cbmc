public class Outer<T>
{
  private class Inner
  {
    private final AbstractGenericClass<T> u;

    Inner (AbstractGenericClass<T> t)
    {
      this.u = t;
    }
  }

  private enum InnerEnum
  {

  }
}

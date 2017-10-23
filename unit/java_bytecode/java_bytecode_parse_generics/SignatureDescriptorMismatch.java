public class SignatureDescriptorMismatch<T>
{
  private class Inner
  {
    private final AbstractGeneric<T> u;

    Inner (AbstractGeneric<T> t)
    {
      this.u = t;
    }
  }

  private enum InnerEnum
  {

  }
}

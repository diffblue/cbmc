public class SignatureDescriptorMismatch<T>
{
  // this models ArrayList.Sublist.<init> for which we were getting an error
  private class Inner
  {
    private final AbstractGeneric<T> u;

    Inner (AbstractGeneric<T> t)
    {
      this.u = t;
    }
  }

  // this models another situation in which the error occurred
  private enum InnerEnum
  {

  }
}

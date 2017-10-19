class SimpleGeneric<T>
{
  public T t;

  public static <T> SimpleGeneric<T> makeGeneric(T value)
  {
    SimpleGeneric<T> newST = new SimpleGeneric<T>();
    newST.t = value;
    return newST;
  }
}

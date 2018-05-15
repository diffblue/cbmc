class Generic<T>
{
  public T t;
  public Generic<Integer> g;

  public static <T> Generic<T> makeGeneric(T value)
  {
    Generic<T> newST = new Generic<T>();
    newST.t = value;
    return newST;
  }
}

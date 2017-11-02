public class GenericFields<T, S> {
  public T f;

  public Generic<T> f2;
  public Generic<Integer> f3;

  public Generic<Generic<T>> f4;
  public Generic<Generic<Generic<Integer>>> f5;

  public GenericTwoParam<T, T> f6;
  public GenericTwoParam<T, S> f7;
  public GenericTwoParam<Integer, T> f8;
  public GenericTwoParam<T, Integer> f9;
  public GenericTwoParam<Integer, String> f10;

  public GenericTwoParam<Generic<T>, GenericTwoParam<S, Integer>> f11;
}

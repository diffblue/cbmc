public class GenericImplementationSimpleMore<T, U> implements GenericInterface<T> {
  T t;
  U u;

  public GenericImplementationSimpleMore(T t, U u) {
    this.t = t;
    this.u = u;
  }

  public int size() {
    return 2;
  }
  public T first() {
    return t;
  }
  public int num() {
    if (u instanceof Bar) {
      return ((Bar) u).get();
    }
    return 1;
  }
}

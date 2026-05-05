public class GenericImplementationMore<T, U> implements GenericInterface<T> {

  T[] elementsT;
  U[] elementsU;

  public GenericImplementationMore(T[] arrayT, U[] arrayU) {
    elementsT = arrayT;
    elementsU = arrayU;
  }

  public int size() {
    return elementsT.length + elementsU.length;
  }

  public T first() {
    return elementsT[0];
  }

  public int num() {
    if (elementsU[0] instanceof Bar) {
      return ((Bar) elementsU[0]).get();
    }
    return elementsU.length;
  }
}

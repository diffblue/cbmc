public class GenericImplementation<T> implements GenericInterface<T> {

  T[] elements;

  public GenericImplementation(T[] array) {
    elements = array;
  }

  public int size() {
    return elements.length;
  }

  public T first() {
    return elements[0];
  }

  public int num() {
    return 5;
  }
}

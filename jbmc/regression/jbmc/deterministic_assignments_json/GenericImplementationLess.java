public class GenericImplementationLess implements GenericInterface<Foo> {

  Foo[] elements;

  public GenericImplementationLess(Foo[] array) {
    elements = array;
  }

  public int size() {
    return elements.length;
  }

  public Foo first() {
    return elements[0];
  }

  public int num() {
    return first().get();
  }

}

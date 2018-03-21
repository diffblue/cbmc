// int wrapper
class IWrapper {
  public int i;
  public IWrapper(int ii) {
    i = ii;
  }
}

// simple generic class
class Wrapper<T> {
  public T field;
  public T[] array_field;
  public int int_field;
}

// generic class with two parameters
class PairWrapper<K, V> {
  public K first;
  public V second;
}

// simple generic interface
interface InterfaceWrapper<T> {
  public T method(T t);
}

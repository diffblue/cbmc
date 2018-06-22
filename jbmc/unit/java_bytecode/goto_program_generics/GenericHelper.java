// int wrapper
class IWrapper {
  public int i;
  public IWrapper(int ii) {
    i = ii;
  }
}

// boolean wrapper
class BWrapper {
  public boolean b;
  public BWrapper(boolean bb) {
    b = bb;
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

// generic interface with two parameters
interface InterfacePairWrapper<K, V> {
  public K method(K k, V v);
}

// generic class with unsupported signature - generic bound
class UnsupportedWrapper1<T extends UnsupportedWrapper1<T>> {
  public T field;
}

// generic class with unsupported signature - multiple bounds
class UnsupportedWrapper2<T extends InterfaceWrapper & InterfacePairWrapper>
{
  public T field;
}

// generic opaque class, make sure the .class file is not available
class OpaqueWrapper<T> {
  public T field;
}

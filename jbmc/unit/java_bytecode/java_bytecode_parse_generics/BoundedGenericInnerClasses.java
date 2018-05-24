public class BoundedGenericInnerClasses
{
  class Inner<E>
  {
    E elem;
  }

  class BoundedInner<NUM extends java.lang.Number>
  {
    NUM elem;

    public void f(NUM x) {
    }
  }

  BoundedInner<Integer> belem;

  class DoubleBoundedInner<T extends java.lang.Number & Interface>
  {
    T elem;
  }

  class TwoElementInner<K, V>
  {
    K k;
    V v;
  }
}

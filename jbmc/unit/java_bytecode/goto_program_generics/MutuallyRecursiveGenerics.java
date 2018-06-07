class Outer<K, V, U> {
  class Inner<U> {
    Outer<V, K, U> o;
    U u;
  }
  Inner<U> inner;
  K key;
  V value;
}
class Three<X, E, U> {
  Three<U, X, E> rotate;
  Three<X, E, U> normal;
  X x;
  E e;
  U u;
}
class KeyValue<K, V> {
    KeyValue<K, V> next;
    KeyValue<V, K> reverse;
    K key;
    V value;
}
class MutuallyRecursiveGenerics {
  KeyValue<String, Integer> example1;
  Three<Byte, Character, Integer> example2;
  Outer<Boolean, Byte, Short> example3;
  void f() {
  }
}

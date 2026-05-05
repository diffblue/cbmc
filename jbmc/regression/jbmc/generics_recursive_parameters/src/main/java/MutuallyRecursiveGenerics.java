class KeyValue<K, V> {
    KeyValue<K, V> next;
    KeyValue<V, K> reverse;
    K key;
    V value;
}
class MutuallyRecursiveGenerics {
  void f() {
    KeyValue<String, Integer> example1 = new KeyValue<>();
    assert example1 != null;
  }
}

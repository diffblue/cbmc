class generic_two_parameters {
  class KeyValuePair<K, V> {
    K key;
    V value;
  }

  KeyValuePair<String, Integer> bomb;

  public String func() {
    KeyValuePair<String, Integer> e = new KeyValuePair<String, Integer>();
    e.key = "Hello";
    e.value = 5;
    if (e.value >= 4) 
    {
        return e.key;
    }
    else 
    {
        return "Oops";
    }
  }
}

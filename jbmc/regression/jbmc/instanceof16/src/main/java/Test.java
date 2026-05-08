public class Test<T> {

  public static void test(String[] args) {
    Object o = null;
    assert !(o instanceof String);
    assert !(o instanceof Object);
    assert !(o instanceof String[]);
    assert !(o instanceof Object[]);
    assert !(o instanceof String[][]);
    assert !(o instanceof Object[][]);
  }
}

public class Test<T> {

  public static void test(String[] args) {

    // Note generic array types like these cannot be tested for in Java
    Test<Integer>[] ts = new Test[1];
    assert ts instanceof Test[];
    assert ts instanceof Object[];
    assert (Object[]) ts instanceof String[];
  }
}

public class Test {

  public static void test(String[] args) {

    Object[] ts = new Test[5];
    assert ts instanceof Test[];
    assert ts instanceof Object[];
    assert ts instanceof String[];
  }
}

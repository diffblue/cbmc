public class Test {

  public static void test(String[] args) {

    Object[] ts = new Test[5];
    Object[] clone = ts.clone();
    assert clone instanceof Test[];
    assert clone instanceof Object[];
    assert clone instanceof String[];
  }
}

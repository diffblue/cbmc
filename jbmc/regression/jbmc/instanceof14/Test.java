public class Test {

  class Inner {}

  public static void test(String[] args) {

    Object[] ts = new Test.Inner[1];
    assert ts instanceof Object[];
    assert ts instanceof Test.Inner[];
    assert ts instanceof Test[];
  }
}

public class Main {
  public void test1() {
    StringBuilder sb = new StringBuilder("abc");
    sb.substring(-1);
  }

  public void test2() {
    StringBuilder sb = new StringBuilder("abc");
    sb.substring(4);
  }

  public void test3() {
    StringBuilder sb = new StringBuilder("abc");
    sb.substring(-1, 4);
  }
}

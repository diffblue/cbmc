public class Test {

  private static Test static_test = new Test();
  private Test test = null;

  public Test() {
  }
  
  public int foo(int x) {
    if (x > 10) {
      return x;
    } else {
      return x * 10;
    }
  }
  
  public void obsolete() {
  }
}

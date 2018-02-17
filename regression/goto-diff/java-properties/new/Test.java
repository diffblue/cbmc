public class Test {

  private static Test static_test = null;
  private Test test = new Test();

  public Test() {
  }
  
  public int foo(int x) {
    if (x > 10) {
      return x;
    } else {
      return x * 10;
    }
  }
  
  public void newfun() {
  }
}

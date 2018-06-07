public class Test {

  @org.cprover.MustNotThrow
  public static void mustNotThrow() {
    throw new RuntimeException("Oh dear");
  }

  public static void main() {
    try {
      mustNotThrow();
    }
    catch(Throwable e) {
      assert false;
    }
  }

}

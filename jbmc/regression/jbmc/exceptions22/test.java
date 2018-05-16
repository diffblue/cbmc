public class test {
  public static void main () {
    try {
      f();
    }
    catch(Exception e) {
      assert(false); // Should be unreachable
    }
  }

  public static void f() {
    try {
      throw new Exception();
    }
    catch(Exception e) {
      // Should prevent main's catch handler from being invoked
    }
  }
}


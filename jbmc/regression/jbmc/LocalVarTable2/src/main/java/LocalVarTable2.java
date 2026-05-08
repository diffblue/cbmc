// Must compile this with -g (produces LocalVarTable) to exhibit bug.

public class LocalVarTable2 {

  public static Object f() {
    for(int i = 0; i < 10; ++i) { System.out.printf("Count %d\n", i); }
    try {
      return new Object();
    }
    finally {
      System.out.println("Finally executed\n");
    }
  }

  public static void main(String[] args) {
    f();
  }

}

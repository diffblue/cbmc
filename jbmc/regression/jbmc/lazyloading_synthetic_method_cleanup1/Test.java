public class Test {

  // Refers to, but never instantiates or refers to static fields of, Unused.
  // Thus a clinit-wrapper for Unused should be created, but subsequently
  // discarded.
  Unused u;

  public static void main() {

  }

}

class Unused {

  static int x;

  static {
    x = 1;
  }

}

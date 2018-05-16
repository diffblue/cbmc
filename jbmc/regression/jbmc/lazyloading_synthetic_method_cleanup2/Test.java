public class Test {

  // Refers to, but never instantiates or refers to static fields of, Unused.
  // Thus a clinit-wrapper for Unused should be created, but subsequently
  // discarded.
  Unused1 u;

  public static void main() {

  }

}

class Unused1 extends Unused2 {

}

class Unused2 {

  static int x;

  static {
    x = 1;
  }

}

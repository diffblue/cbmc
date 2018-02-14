public class Test {

  public static void main() {

  }

  public static Opaque unused() {

    // Should cause jbmc to create a synthetic static initialiser for Opaque,
    // but because this function isn't called by main() it should then be
    // cleaned up as unused.
    return Opaque.field;

  }

}

class Opaque {

  public static Opaque field;

}

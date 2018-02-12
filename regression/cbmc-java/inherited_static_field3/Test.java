public class Test extends OpaqueParent {

  public static void main() {

    assert x == OpaqueParent.x;

  }

}

class OpaqueParent {

  public static int x;

}

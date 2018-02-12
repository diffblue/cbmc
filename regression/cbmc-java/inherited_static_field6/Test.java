public class Test extends OpaqueParent {

  public static void main(int nondet) {

    x = nondet;
    assert x == Grandparent.x;

  }

}

class OpaqueParent extends Grandparent {

  public static int x;

}

class Grandparent {

  public static int x;

}

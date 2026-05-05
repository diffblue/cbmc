public class Test extends Parent {

  public static void main(int nondet) {

    x = nondet;
    assert x == Parent.x;
    assert x == OpaqueGrandparent.x;

  }

}

class Parent extends OpaqueGrandparent {

  public static int x;

}

class OpaqueGrandparent {

  public static int x;

}

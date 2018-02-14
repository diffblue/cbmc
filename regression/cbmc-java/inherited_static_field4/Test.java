public class Test extends Parent {

  public static void main(int nondet) {

    x = nondet;
    assert x == Grandparent.x;

  }

}

class Parent extends Grandparent {

  public static int x;

}

class Grandparent {

  public static int x;

}

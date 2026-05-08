public class Test extends Parent {

  public static void main(int nondet) {

    x = nondet;
    assert x == Parent.x;

  }

}

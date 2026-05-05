public class Test {

  public static void main(int argc) {

    A a = argc == 1 ? new A() : null;
    a.field.virtualmethod();

  }

}

class A {

  public B field;

  public A() {
    field = new B();
  }

}

class B {

  public void virtualmethod() { }

}

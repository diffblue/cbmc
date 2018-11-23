public class VirtualCallNullChecks {

  public static void main() {

    A a = new A();
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

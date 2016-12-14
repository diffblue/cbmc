
public class A {

  int f() {
    return 1;
  }

  public void main(int unknown) {

    A a = new A();
    B b = new B();
    C c = new C();
    A callee;
    switch(unknown) {
      case 1:
        callee = a;
        break;
      case 2:
        callee = b;
        break;
      default:
        callee = c;
         break;
    }

    callee.f();

  }

}

class B extends A {

  int f() {
    return 2;
  }

}

class C extends B {}

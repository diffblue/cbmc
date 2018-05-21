/* 
old.jar needs to be created by first adding B.class and Test.class and then
updated to add A.class. This makes the class loader load the classes A and B
in reverse order.
*/

class A {
  boolean bar() {
    return true;
  }
}

class B extends A {
  boolean bar() {
    return false;
  }
}

public class Test {

  public boolean foo(A x) {
    return x.bar();
  }
}

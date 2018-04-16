/* 
old.jar needs to be created by first adding B.class and Test.class and then
updated to add A.class. This makes the class loader load the classes A and B
in reverse order.
*/

class A {
}

class B extends A {
}

public class Test {

  public boolean foo(A x) {
    if (x instanceof A) {
      return true;
    } else {
      return false;
    }
  }
}

class A {
  int val;
}

class B {
  int getVal(A a) {
    return a.val;
  }
}

class pointer_check1 {
  public static void main(String[] args) {
    B b = new B();
    int myval = b.getVal(null);
  }
}

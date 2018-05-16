interface A {
  public int f();
}
interface B {
  public int g();
}

class O {
  public String toString() {
    return "O";
  }
}

class D extends O implements A, B {
  public int f() {
    return 0;
  }
  public int g() {
    return 1;
  }
}

class C extends D {
  public String toString() {
    return "C";
  }
}

class E {
  C c;
  D d;
  String f(Object o) {
    return o.toString();
  }
}

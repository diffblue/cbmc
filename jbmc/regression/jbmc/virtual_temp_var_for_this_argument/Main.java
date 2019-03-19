class A {
  public void f() {}
}

class B extends A {
  public void f() {}
}

class AContainer {
  A a_field;
}

public class Main {

  public static void oneCandidate(B b) { b.f(); }

  public static void twoCandidatesNoDerefs(A a) {
    // Make sure B is also loaded
    B unusedB = new B();

    a.f();
  }

  public static void twoCandidatesWithDerefs(AContainer aContainer) {
    // Make sure B is also loaded
    B unusedB = new B();

    aContainer.a_field.f();
  }
}

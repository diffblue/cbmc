import org.cprover.CProver;

class A {
  int x;

  public void cproverNondetInitialize() { CProver.assume(x == 42); }
}

class B extends A {}

class C extends B {}

class F extends A {
  public void cproverNondetInitialize() {}
}

interface I {
}

class J extends A implements I {
}

class K extends A {
  int y;

  public void cproverNondetInitialize() {
    super.cproverNondetInitialize();
    CProver.assume(y == 6);
  }
}

abstract class M {
  int x;

  public void cproverNondetInitialize() { CProver.assume(x == 42); }
}

class N extends M {}

public class Test {

  void inheritanceTwoLevels(C c) {
    if (c != null)
      assert (c.x == 42);
  }

  void override(F f) {
    if (f != null)
      assert (f.x == 42);
  }

  void callingSuperCproverNondetInitialize(K k) {
    if (k != null) {
      assert (k.x == 42);
      assert (k.y == 6);
    }
  }

  void inheritanceFromAbstractClass(N n) {
    if (n != null)
      assert (n.x == 42);
  }

  void alsoImplementsInterface(J j) {
    if (j != null)
        assert (j.x == 42);
    }
}

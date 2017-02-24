import org.cprover.CProver;

class A { }

class B { A a; }

class C { B b; }

class NondetGenericWithoutNull
{
  static void foo()
  {
    C c = null;
    CProver.nondetWithoutNull(c);
    assert c != null;
  }
}

import org.cprover.CProver;

class A { }

class B { A a; }

class NondetGenericWithoutNull
{
  static void foo()
  {
    B b = null;
    CProver.nondetWithoutNull(b);
    assert b != null;
  }
}

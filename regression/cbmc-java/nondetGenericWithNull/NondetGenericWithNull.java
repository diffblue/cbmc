import org.cprover.CProver;

class A { }

class B { A a; }

class NondetGenericWithNull
{
  static void foo()
  {
    B b = null;
    CProver.nondetWithNull(b);
    assert b != null;
  }
}

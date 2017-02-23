import org.cprover.CProver;

class A { }

class B { A a; }

class NondetGenericWithoutNull
{
  static void foo()
  {
    B b = CProver.nondetWithoutNull();
    assert b == null;
  }
}

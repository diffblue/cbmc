import org.cprover.CProver;

class A { }

class B { A a; }

class NondetGenericWithNull
{
  static void foo()
  {
    B b = CProver.nondetWithNull();
    assert b == null;
  }
}

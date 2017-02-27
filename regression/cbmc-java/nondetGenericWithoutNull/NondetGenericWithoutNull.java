import org.cprover.CProver;

class B { int a; }

class C { B b; }

class NondetGenericWithoutNull
{
  static void foo()
  {
    C c = CProver.nondetWithoutNull();
    assert c != null;
  }
}

import org.cprover.CProver;

class B { int a; }

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

import org.cprover.CProver;

class B { int a; }

class NondetGenericWithoutNull
{
  static void main()
  {
    B b = CProver.nondetWithoutNull();
    assert b != null;
  }
}

import org.cprover.CProver;

class B { int a; }

class NondetGenericWithNull
{
  static void main()
  {
    B b = CProver.nondetWithNull();
    assert b != null;
    assert b.a != 0;
  }
}

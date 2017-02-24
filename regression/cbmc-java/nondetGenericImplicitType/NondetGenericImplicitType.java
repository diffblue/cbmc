import org.cprover.CProver;

class Foo { }

class NondetGenericImplicitType
{
  static void foo()
  {
    Foo x = null;
    CProver.nondetWithNull(x);
    assert x == null;
  }
}

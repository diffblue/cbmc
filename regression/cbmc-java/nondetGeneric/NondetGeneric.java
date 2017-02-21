import org.cprover.CProver;

class Foo { }

class NondetGeneric
{
  static void callWithoutExplicitType()
  {
    //  User may cast to incompatible type.
    Foo foo = CProver.nondet();
    assert foo == null;
  }

  static void callWithoutAssigningResult()
  {
    assert CProver.nondet() == null;
  }
}

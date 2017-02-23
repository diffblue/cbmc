import org.cprover.CProver;

class Foo { }

class NondetGenericImplicitType
{
  static void callWithImplicitType()
  {
    //  User may cast to incompatible type.
    Foo foo = CProver.nondetWithNull();
    assert foo == null;
  }
}

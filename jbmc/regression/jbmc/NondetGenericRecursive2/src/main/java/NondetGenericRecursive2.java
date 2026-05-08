import org.cprover.CProver;

class A
{
}

class B
{
  A a;
}

class C
{
  B b;
}

class NondetGenericRecursive2
{
  static void main()
  {
    C c = CProver.nondetWithNull(null);
    CProver.assume(c != null);
    CProver.assume(c.b != null);
    CProver.assume(c.b.a != null);
    assert c.b.a != null;
  }
}

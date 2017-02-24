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
  static void foo()
  {
    C c = null;
    CProver.nondetWithoutNull(c);
    assert c.b.a != null;
  }
}

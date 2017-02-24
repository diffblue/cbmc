import org.cprover.CProver;

class A
{
  int[] ints = new int[10];
}

class B
{
  A a;
}

class C
{
  B b;
}

class NondetGenericArray
{
  static void foo()
  {
    C c = null;
    CProver.nondetWithoutNull(c);
    assert c.b.a != null;
    assert c.b.a.ints != null;
  }
}

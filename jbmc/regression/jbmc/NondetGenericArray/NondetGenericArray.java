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
  static void main()
  {
    C c = CProver.nondetWithNull();
    CProver.assume(c != null);
    CProver.assume(c.b != null);
    CProver.assume(c.b.a != null);
    CProver.assume(c.b.a.ints != null);
    assert c.b.a != null;
    assert c.b.a.ints != null;
  }
}

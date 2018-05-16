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

class NondetGenericRecursive
{
  static void main()
  {
    C c = CProver.nondetWithNull();
    assert c == null;
  }
}

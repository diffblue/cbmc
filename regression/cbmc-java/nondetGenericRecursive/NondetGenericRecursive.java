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
  static void foo()
  {
    C c = CProver.nondetWithNull();
    assert c == null;
  }
}

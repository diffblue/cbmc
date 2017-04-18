import org.cprover.CProver;

class A
{
  int a;
}

class NondetDirectFromMethod
{
  A methodReturningA()
  {
    return CProver.nondetWithoutNull();
  }

  void main()
  {
    assert methodReturningA() != null;
  }
}

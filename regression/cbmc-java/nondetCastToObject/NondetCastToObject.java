import org.cprover.CProver;

class NondetCastToObject
{
  void foo()
  {
    Object o = CProver.nondetWithNull();
    CProver.assume(o != null);
    assert o != null;
  }
}

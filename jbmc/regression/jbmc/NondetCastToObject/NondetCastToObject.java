import org.cprover.CProver;

class NondetCastToObject
{
  void main()
  {
    Object o = CProver.nondetWithNull();
    CProver.assume(o != null);
    assert o != null;
  }
}

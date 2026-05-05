import org.cprover.CProver;

class NondetCastToObject
{
  void main()
  {
    Object o = CProver.nondetWithNull(null);
    CProver.assume(o != null);
    assert o != null;
  }
}

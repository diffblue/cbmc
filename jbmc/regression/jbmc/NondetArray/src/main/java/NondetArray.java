import org.cprover.CProver;

class NondetArray
{
  void main()
  {
    Object[] obj = CProver.nondetWithoutNull(null);
    assert obj != null;
  }
}

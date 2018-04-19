import org.cprover.CProver;

class NondetArray
{
  void main()
  {
    Object[] obj = CProver.<Object[]>nondetWithoutNull();
    assert obj != null;
  }
}

import org.cprover.CProver;

class NondetBoolean
{
  static void main()
  {
    boolean x = CProver.nondetBoolean();
    assert x == false;
  }
}

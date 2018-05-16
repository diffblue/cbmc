import org.cprover.CProver;

class NondetStringBuilder
{
  static void main()
  {
    StringBuilder x = CProver.nondetWithNull();
    assert x == null || x instanceof StringBuilder;
  }
}

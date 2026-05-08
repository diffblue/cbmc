import org.cprover.CProver;

class NondetStringBuilder
{
  static void main()
  {
    StringBuilder x = CProver.nondetWithNull(null);
    assert x == null || x instanceof StringBuilder;
  }
}

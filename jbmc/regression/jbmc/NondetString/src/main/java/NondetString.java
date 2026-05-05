import org.cprover.CProver;

class NondetString
{
  static void main()
  {
    String x = CProver.nondetWithNull(null);
    assert x == null || x instanceof String;
  }
}

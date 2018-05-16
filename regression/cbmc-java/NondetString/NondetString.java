import org.cprover.CProver;

class NondetString
{
  static void main()
  {
    String x = CProver.nondetWithNull();
    assert x == null || x instanceof String;
  }
}

import org.cprover.CProver;

class NondetStringBuffer
{
  static void main()
  {
    StringBuffer x = CProver.nondetWithNull(null);
    assert x == null || x instanceof StringBuffer;
  }
}

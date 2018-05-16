import org.cprover.CProver;

class NondetStringBuffer
{
  static void main()
  {
    StringBuffer x = CProver.nondetWithNull();
    assert x == null || x instanceof StringBuffer;
  }
}

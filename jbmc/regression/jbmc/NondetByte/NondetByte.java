import org.cprover.CProver;

class NondetByte
{
  static void main()
  {
    byte x = CProver.nondetByte();
    assert x == 0;
  }
}

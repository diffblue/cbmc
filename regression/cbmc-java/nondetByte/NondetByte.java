import org.cprover.CProver;

class NondetByte
{
  static void foo()
  {
    byte x = CProver.nondetByte();
    assert x == 0;
  }
}

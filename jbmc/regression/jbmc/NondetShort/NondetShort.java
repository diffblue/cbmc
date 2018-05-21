import org.cprover.CProver;

class NondetShort
{
  static void main()
  {
    short x = CProver.nondetShort();
    assert x == 0;
  }
}

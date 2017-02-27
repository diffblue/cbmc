import org.cprover.CProver;

class NondetShort
{
  static void foo()
  {
    short x = CProver.nondetShort();
    assert x == 0;
  }
}

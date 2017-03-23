import org.cprover.CProver;

class NondetLong
{
  static void foo()
  {
    long x = CProver.nondetLong();
    assert x == 0;
  }
}

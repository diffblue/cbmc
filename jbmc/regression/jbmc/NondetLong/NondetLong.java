import org.cprover.CProver;

class NondetLong
{
  static void main()
  {
    long x = CProver.nondetLong();
    assert x == 0;
  }
}

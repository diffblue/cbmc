import org.cprover.CProver;

class NondetInt
{
  static void foo()
  {
    int x = CProver.nondetInt();
    assert x == 0;
  }
}

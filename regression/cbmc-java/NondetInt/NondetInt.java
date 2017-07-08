import org.cprover.CProver;

class NondetInt
{
  static void main()
  {
    int x = CProver.nondetInt();
    assert x == 0;
  }
}

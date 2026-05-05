import org.cprover.CProver;

class NondetDouble
{
  static void main()
  {
    double x = CProver.nondetDouble();
    assert x == 0;
  }
}

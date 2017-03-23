import org.cprover.CProver;

class NondetDouble
{
  static void foo()
  {
    double x = CProver.nondetDouble();
    assert x == 0;
  }
}

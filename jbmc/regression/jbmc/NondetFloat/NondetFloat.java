import org.cprover.CProver;

class NondetFloat
{
  static void main()
  {
    float x = CProver.nondetFloat();
    assert x == 0;
  }
}

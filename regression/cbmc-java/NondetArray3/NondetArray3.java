import org.cprover.CProver;

class NondetArray3
{
  void main()
  {
    Integer[] ints = CProver.nondetWithoutNull();
    assert ints != null;

    int num = 0;
    for (Integer i : ints) {
      num *= i.intValue();
    }
    assert num == 0;
  }
}

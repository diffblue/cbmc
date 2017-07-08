import org.cprover.CProver;

class NondetArray2
{
  void main()
  {
    Integer[] ints = CProver.nondetWithoutNull();

    int num = 0;
    for (Integer i : ints) {
      num *= i.intValue();
    }
    assert num == 0;
  }
}

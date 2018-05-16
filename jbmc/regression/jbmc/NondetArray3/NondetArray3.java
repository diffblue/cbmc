import org.cprover.CProver;

class NondetArray3
{
  void main()
  {
    Integer[] ints = CProver.nondetWithoutNull();
    assert ints != null;

    int num = 0;
    for (Integer i : ints) {
      if(i == null)
        continue;
      num *= i.intValue();
    }
    assert num == 0;
  }
}

import org.cprover.CProver;

class NondetAssume1
{
  void main()
  {
    int x = CProver.nondetInt();
    CProver.assume(x == 1);
    assert x == 1;
  }
}

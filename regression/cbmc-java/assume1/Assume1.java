import org.cprover.CProver;

class Assume1
{
  static void foo(int x)
  {
    CProver.assume(x>3);
    assert x>0;
  }
}

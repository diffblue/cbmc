import org.cprover.CProver;

class Assume2
{
  static void foo(int x)
  {
    CProver.assume(x>3);    
    assert x>4;
  }
}

import org.cprover.CProver;

class Assume3
{
  public static void main(String[] args)
  {
    CProver.assume(false);
    assert false;
  }
}

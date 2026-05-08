import org.cprover.CProver;
class test
{
  public static void main(String[] args)
  {
    int i=CProver.nondetInt();
    assert(i!=0);
  }
}


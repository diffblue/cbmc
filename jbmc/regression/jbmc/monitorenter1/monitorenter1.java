public class monitorenter1
{
  public int doIt(int what)
  {
    int some;
    
    synchronized(this) {
      some=what;
    }

    return some;
  }

  public void test()
  {
    assert doIt(1)==1;
  }
}

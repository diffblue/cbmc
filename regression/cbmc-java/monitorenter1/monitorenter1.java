public class monitorenter1
{
  public boolean doIt(boolean b)
  {
    boolean a;
    synchronized(this) {
      a = !b;
    }
    return a;
  }

  public void test()
  {
    assert doIt(false);
  }
}
